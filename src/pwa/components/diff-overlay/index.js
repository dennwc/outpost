// Diff review overlay + source control (git status/log/commit/push/pull,
// branch rename, commit-and-ship). Mount-parameterized: builds its own DOM
// into #diff-overlay-root on open, tears it fully down on close — no
// getElementById singletons baked into markup (index.html only carries the
// empty mount anchor).
//
// Consumers:
//   - app.js calls initDiffOverlay({ renderSession, startThinking,
//     scrollTranscriptBottom, leaveSession }) once at startup.
//   - app-bridge's openDiffForStep({sessionId, jobId?, stepId?}) — filled
//     here via installAppBridge() — is how Tracked's step CTA opens a review
//     scoped to a specific job/step without importing this module directly.
//   - openDiffOverlay(opts) also accepts no-args (falls back to the current
//     session) for legacy callers (mobile-header's git button, the desktop
//     session-view git button via app-bridge's openDiffForSession).

import { escapeHtml } from '../../util.js';
import { sendUserMessage as tabSendUserMessage } from '../session-view/session-ws.js';
import { sessions } from '../../state/sessions.js';
import { work } from '../../state/work.js';
import { isDesktop } from '../../layout/index.js';
import { keymap } from '../../state/keymap.js';
import { installAppBridge, showStatusToast } from '../../app-bridge.js';
import { registerBackHandler } from '../mobile-shell/history.js';
import { draftCommitMessage } from '../../utils/commit-message.js';
import {
  diffState,
  sourceCtl,
  resetGitState,
  getHeader as getGitHeader,
  setHeader as setGitHeader,
  getBusy as getGitBusy,
  setBusy as setGitBusy,
} from '../../state/git.js';
import { worktreeChanges } from '../../state/worktree-changes.js';
import { formatDiffReviewMessage as formatDiffReviewMessageShared } from '../diff-review-format.js';
import { gapsFor, gapRows, lastNewLine } from '../../utils/diff-gaps.js';
import { buildFileTree } from '../../utils/file-tree.js';
import { makeSheetDismissible, noteSheetOpen, noteSheetClose, confirmInSheet } from '../sheet-utils.js';

let _deps = {
  renderSession: () => {},
  startThinking: () => {},
  scrollTranscriptBottom: () => {},
  leaveSession: () => {},
};

const DIFF_STATUS_ICON = { added: 'A', modified: 'M', deleted: 'D', renamed: 'R', copied: 'C' };

// Mobile-only: the file list collapses into a tap-to-toggle top strip (P3
// brief) instead of desktop's always-visible rail. Overlay-instance state,
// reset whenever a fresh diff review opens.
let filesStripOpen = false;

function cssEscape(s) { return String(s).replace(/["\\]/g, '\\$&'); }
function diffCommentKey(file, side, line) { return `${file}:${side}:${line}`; }

// ── Context resolution ───────────────────────────────────────────────────
// Resolves the job/step behind a sessionId/jobId/stepId triple so the header and
// commit-message draft can speak in terms of "step 2 · Draft the fix" instead of
// a bare branch name.
function findStepContext({ jobId, stepId, sessionId }) {
  const { byId, jobs } = work.get();
  let job = jobId ? byId.get(jobId) ?? null : null;
  let step = job && stepId ? job.steps.find((s) => s.id === stepId) ?? null : null;

  if (!job) {
    outer: for (const j of jobs) {
      for (const s of j.steps) {
        if (s.sessionId === sessionId) { job = j; step = s; break outer; }
      }
    }
  }
  return { job, step };
}

function buildDiffContext({ sessionId, jobId, stepId }) {
  const found = findStepContext({ jobId, stepId, sessionId });
  return {
    sessionId,
    jobId: found.job?.id ?? jobId ?? null,
    stepId: found.step?.id ?? stepId ?? null,
    job: found.job ?? null,
    step: found.step ?? null,
  };
}

function stepOrdinal(job, step) {
  if (!job || !step) return null;
  const i = job.steps.findIndex((s) => s.id === step.id);
  return i >= 0 ? i + 1 : null;
}

function defaultCommit(ctx, status) {
  const message = draftCommitMessage(ctx, 0);
  const currentBranch = status?.branch ?? '';
  const base = status?.worktree?.baseBranch ?? status?.defaultBranch ?? 'main';
  const suggested = ctx?.step ? `fix/${slugify(ctx.step.title)}` : (currentBranch || 'fix/change');
  return {
    message,
    autoFilled: message.length > 0,
    variant: 0,
    push: true,
    // Once a PR is open on this branch, a round appends — "open PR" would re-squash to
    // base and diverge from the pushed head. Default it off so the action is a plain
    // commit-on-top + fast-forward push.
    openPr: !(ctx?.step?.pr?.prUrl || status?.prUrl),
    mergeMode: 'squash-to-branch',
    newBranch: base === currentBranch || !currentBranch ? suggested : currentBranch,
    // The PR's own title/description, used only once the squash collapses several rounds (see
    // needsPrDraft). prDraft: idle → drafting → ready | error.
    prTitle: '',
    prBody: '',
    prDraft: 'idle',
    prError: '',
  };
}

// ── PR draft, for a branch several rounds committed to ────────────────────
// How many rounds this squash collapses: the commits already on the branch since its base, plus
// the uncommitted round the button commits first. Up to one, the commit box's message already
// describes the whole branch and `gh pr create --fill` publishes it. Past one, that message is
// only the last round's, so the PR gets its own title and description, drafted by Claude from the
// job and the whole branch (POST git/pr-draft).
function squashRounds(s) {
  return (s?.worktree?.commitsSinceBase ?? 0) + (s?.clean ? 0 : 1);
}

function needsPrDraft() {
  const s = sourceCtl.status;
  const c = diffState.commit;
  return Boolean(s?.worktree) && c.mergeMode === 'squash-to-branch' && c.openPr && !s?.prUrl && squashRounds(s) >= 2;
}

// Per session, keyed on the branch state it was drafted from, so reopening the overlay on an
// unchanged branch doesn't spend another draft.
const prDraftCache = new Map();
const prDraftKey = (s) => `${s?.worktree?.commitsSinceBase ?? 0}:${s?.clean ? 'clean' : 'dirty'}`;

function ensurePrDraft() {
  const sessionId = diffState.ctx?.sessionId;
  const c = diffState.commit;
  if (!sessionId || !c || c.prDraft !== 'idle' || !needsPrDraft()) return;
  const cached = prDraftCache.get(sessionId);
  if (cached && cached.key === prDraftKey(sourceCtl.status)) {
    Object.assign(c, { prTitle: cached.title, prBody: cached.body, prDraft: 'ready' });
    return;
  }
  void draftPr(sessionId);
}

async function draftPr(sessionId) {
  const c = diffState.commit;
  const key = prDraftKey(sourceCtl.status);
  c.prDraft = 'drafting';
  c.prError = '';
  paintPrDraft();
  try {
    const r = await fetch(`/api/sessions/${encodeURIComponent(sessionId)}/git/pr-draft`, { method: 'POST' });
    const body = await r.json().catch(() => null);
    if (diffState.commit !== c) return; // the overlay moved on to another session meanwhile
    if (!r.ok || !body?.title) throw new Error(body?.error || `HTTP ${r.status}`);
    // Text the user already started typing wins over the draft.
    if (!c.prTitle.trim()) c.prTitle = body.title;
    if (!c.prBody.trim()) c.prBody = body.body;
    c.prDraft = 'ready';
    prDraftCache.set(sessionId, { key, title: body.title, body: body.body });
  } catch (err) {
    if (diffState.commit !== c) return;
    c.prDraft = 'error';
    c.prError = String(err?.message ?? err);
  }
  paintPrDraft();
}

function prDraftStatus(c) {
  if (c.prDraft === 'drafting') return '◐ drafting with Claude…';
  if (c.prDraft === 'error') return 'draft failed';
  if (c.prDraft === 'ready') return `◐ drafted from ${squashRounds(sourceCtl.status)} rounds`;
  return '';
}

// A finished draft fills the fields in place rather than repainting the dialog, which would take
// focus out of whatever the user is typing meanwhile. Falls back to a repaint when the fields
// aren't on screen yet (or anymore).
function paintPrDraft() {
  const c = diffState.commit;
  const title = document.querySelector('.dr-pr-draft .dr-pr-title');
  if (!title) { renderFooter(); renderCommitSheet(); return; }
  const body = document.querySelector('.dr-pr-draft .dr-pr-body');
  if (document.activeElement !== title) title.value = c.prTitle;
  if (body && document.activeElement !== body) body.value = c.prBody;
  const status = document.querySelector('.dr-pr-draft .dr-pr-status');
  if (status) { status.textContent = prDraftStatus(c); status.title = c.prError; }
  const redraft = document.querySelector('.dr-pr-draft .dr-pr-redraft');
  if (redraft) redraft.disabled = c.prDraft === 'drafting';
}

function slugify(s) {
  return String(s || '').toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, '').slice(0, 44) || 'change';
}

// ── Mount lifecycle ───────────────────────────────────────────────────────
let mountEl = null;
function getMount() { return mountEl ?? (mountEl = document.getElementById('diff-overlay-root')); }

// Hardware back closes the overlay instead of popping a screen — see
// mobile-shell/history.js's registry. Re-opening while already open
// (switching session) re-registers rather than stacking a second entry.
let unregisterDiffBack = null;

async function openDiffOverlay(opts = {}) {
  const sessionId = opts.sessionId ?? sessions.get().currentSessionId;
  if (!sessionId) return;
  unregisterDiffBack?.();
  unregisterDiffBack = registerBackHandler(closeDiffOverlay);

  diffState.ctx = buildDiffContext({ sessionId, jobId: opts.jobId, stepId: opts.stepId });
  diffState.comments.clear();
  diffState.openDraftKey = null;
  diffState.draftRange = null;
  diffState.collapsed.clear();
  diffState.collapsedDirs.clear();
  diffState.filter = '';
  diffState.hoveredRowKey = null;
  diffState.refs.branch = currentSessionBranchHint(sessionId);
  diffState.refs.worktree = { base: 'HEAD', head: 'working tree' };
  clearDiffSendWarning();
  filesStripOpen = false;

  mount();
  document.body.style.overflow = 'hidden';
  setSourceFeedback();
  await refreshSourceControl(sessionId);
  diffState.commit = defaultCommit(diffState.ctx, sourceCtl.status);
  diffState.mode = (sourceCtl.status && !sourceCtl.status.clean) ? 'worktree' : 'branch';
  renderCompareModes();
  fetchAndRenderDiff();
}

function openDiffForStep({ jobId, stepId, sessionId } = {}) {
  return openDiffOverlay({ jobId, stepId, sessionId });
}

function currentSessionBranchHint(sessionId) {
  const { projects } = sessions.get();
  for (const p of projects ?? []) {
    const s = p.sessions?.find((s) => s.id === sessionId);
    if (s?.worktreeBranch) return { base: 'main', head: s.worktreeBranch };
  }
  return { base: '…', head: '…' };
}

function closeDiffOverlay() {
  closeCommitSheet();
  unregisterDiffBack?.();
  unregisterDiffBack = null;
  const m = getMount();
  if (m) m.innerHTML = '';
  document.body.style.overflow = '';
  diffState.ctx = null;
}

// Wipe every trace of the previous session's git viewer. Called from app.js on
// session leave so the next session's viewer starts clean.
function resetGitViewer() {
  resetGitState();
  closeDiffOverlay();
}

function mount() {
  const m = getMount();
  if (!m) return;
  m.innerHTML = overlayShellHtml();
  wireOverlayEvents(m);
}

// ── Markup ────────────────────────────────────────────────────────────────
function overlayShellHtml() {
  const ctx = diffState.ctx;
  const stepRef = ctx?.step ? `<span class="o-ref">Step ${stepOrdinal(ctx.job, ctx.step) ?? '?'}</span>` : '';
  const titleLead = ctx?.step ? `Review changes · ${escapeHtml(ctx.step.title)}` : 'Review changes';
  return `
  <div class="dr-scrim" data-act="scrim">
    <div class="dr-overlay" role="dialog" aria-modal="true" aria-label="Diff review">
      <header class="dr-hdr">
        <div class="dr-hdr-title">${stepRef}${titleLead}</div>
        <div class="dr-hdr-stats" id="dr-hdr-stats"></div>
        <div class="dr-hdr-actions">
          <button class="o-btn o-btn--danger dr-btn" type="button" data-act="discard-all"
            title="Discard all uncommitted changes in this worktree">Discard all</button>
          <button class="o-btn o-btn--default dr-btn" type="button" data-act="open-editor"
            title="Opens this checkout on the daemon host, using the command set in Settings > External editor.">Open in editor ↗</button>
          <button class="dr-close" type="button" data-act="close" aria-label="Close">✕</button>
        </div>
      </header>
      <nav class="dr-compare" id="dr-compare" role="tablist" aria-label="View"></nav>
      <div class="dr-warning" id="dr-warning" hidden></div>
      <div class="dr-feedback" id="dr-feedback" hidden></div>
      <div class="dr-body" id="dr-body">
        <nav class="dr-files" aria-label="Files">
          <input class="dr-file-search" id="dr-file-search" type="search" placeholder="Filter files…" autocomplete="off">
          <div class="dr-files-hdr o-microhead" id="dr-files-hdr"></div>
          <div class="dr-files-list" id="dr-files-list"></div>
        </nav>
        <main class="dr-viewport" id="dr-viewport"></main>
        <div class="dr-log" id="dr-log" hidden></div>
      </div>
      <footer class="dr-foot" id="dr-foot"></footer>
    </div>
  </div>`;
}

function wireOverlayEvents(m) {
  m.querySelector('[data-act="scrim"]').addEventListener('click', (e) => {
    if (e.target.dataset.act === 'scrim') closeDiffOverlay();
  });
  m.querySelector('[data-act="close"]').addEventListener('click', closeDiffOverlay);
  m.querySelector('[data-act="discard-all"]').addEventListener('click', () => { void discardAll(); });
  m.querySelector('[data-act="open-editor"]').addEventListener('click', () => { void openInEditor(); });
  m.querySelector('#dr-file-search').addEventListener('input', (e) => {
    diffState.filter = e.target.value;
    renderDiffFileList();
  });
  // Mobile-only: tapping the file-list header toggles the collapsible top
  // strip (desktop's rail stays permanently expanded — toggling it there
  // would just hide the always-visible file rail for no reason).
  m.querySelector('#dr-files-hdr').addEventListener('click', () => {
    if (isDesktop()) return;
    filesStripOpen = !filesStripOpen;
    renderDiffFileList();
  });
  m.querySelector('#dr-viewport').addEventListener('click', onDiffContentClick);
  m.querySelector('#dr-viewport').addEventListener('mouseover', (e) => {
    const row = e.target.closest('.dr-row');
    diffState.hoveredRowKey = row && !row.classList.contains('dr-row-empty') ? rowKey(row) : null;
  });
  m.querySelector('#dr-viewport').addEventListener('change', (e) => {
    const cb = e.target.closest('.dr-file-stage input');
    if (!cb) return;
    const path = cb.dataset.file;
    const card = cb.closest('.dr-file-card');
    if (!path || !card) return;
    const action = cb.checked ? 'stage' : 'unstage';
    if (action === 'stage') { diffState.collapsed.add(path); card.classList.add('is-collapsed', 'is-staged'); }
    else { diffState.collapsed.delete(path); card.classList.remove('is-collapsed', 'is-staged'); }
    stageFileFromUi(diffState.ctx?.sessionId, path, action);
  });
}

function onGlobalKeydown(e) {
  if (!getMount()?.firstElementChild) return; // overlay not open
  const typing = e.target.closest('input, textarea, [contenteditable="true"]');
  if (e.key === 'Escape') { onEscape(e, typing); return; }
  if (keymap.matches(e, 'diff.commentExtend') && !typing && diffState.hoveredRowKey && diffState.draftRange) {
    e.preventDefault();
    const row = findRowByKey(diffState.hoveredRowKey);
    if (row) extendDraftTo(row);
    return;
  }
  if (keymap.matches(e, 'diff.comment') && !typing && diffState.hoveredRowKey && !diffState.openDraftKey) {
    e.preventDefault();
    const row = getMount().querySelector(`.dr-row[data-key="${cssEscape(diffState.hoveredRowKey)}"]`);
    if (row) openCommentFromRow(row);
    return;
  }
  if (keymap.matches(e, 'diff.primaryAction')) {
    const foot = getMount().querySelector('#dr-foot');
    if (foot && !typing) { e.preventDefault(); runPrimaryAction(); }
  }
  if (keymap.matches(e, 'diff.regenerate') && diffState.ctx?.step) {
    e.preventDefault();
    diffState.commit.variant += 1;
    diffState.commit.message = draftCommitMessage(diffState.ctx, diffState.commit.variant);
    diffState.commit.autoFilled = true;
    renderFooter();
  }
}

// Each Escape backs out one level — leave the draft's textarea, stop range-picking, drop the draft — before it closes the overlay.
function onEscape(e, typing) {
  const form = getMount().querySelector('.dr-comment-form');
  if (typing) {
    if (form?.contains(e.target)) form.querySelector('.dr-comment-range-toggle')?.focus();
    return;
  }
  if (diffState.draftRange?.selecting) { setRangeSelecting(form, false); return; }
  if (form) {
    const { editingKey } = diffState.draftRange ?? {};
    const card = form.closest('.dr-file-card');
    form.querySelector('.dr-comment-cancel')?.click();
    const chip = editingKey && card.querySelector(`.dr-comment-card[data-key="${cssEscape(editingKey)}"]`);
    (chip?.querySelector('.dr-comment-link') ?? card.querySelector('.dr-file-card-head'))?.focus({ preventScroll: true });
    return;
  }
  closeDiffOverlay();
}

function rowKey(row) { return diffCommentKey(row.dataset.file, row.dataset.side, row.dataset.line); }

// The editor opens on the DAEMON host, not on this device — that's the only machine the
// worktree exists on. Which command runs there is Settings > External editor.
async function openInEditor() {
  const sessionId = diffState.ctx?.sessionId;
  if (!sessionId) {
    setSourceFeedback('err', 'No session for this diff — nothing to open.');
    return;
  }
  setSourceFeedback('ok', 'Opening…');
  try {
    const res = await fetch(`/api/sessions/${encodeURIComponent(sessionId)}/open-editor`, { method: 'POST' });
    const body = await res.json().catch(() => ({}));
    if (!res.ok) {
      setSourceFeedback('err', body.error || `Open in editor failed (${res.status}).`);
      return;
    }
    setSourceFeedback('ok', `Opened ${body.path} with ${body.command}.`);
  } catch {
    setSourceFeedback('err', 'Open in editor failed — the daemon is unreachable.');
  }
}

// ── Discard (destructive) ─────────────────────────────────────────────────
// Backend refuses non-worktree sessions (it will never wipe a primary
// checkout), so both entry points check status.worktree up front for a clear
// message instead of a 400.
async function discardAll() {
  if (!sourceCtl.status?.worktree) {
    setSourceFeedback('err', 'Discard is only available for worktree sessions — it would wipe uncommitted changes in your primary checkout.');
    return;
  }
  const ok = isDesktop()
    ? confirm('Discard ALL uncommitted changes on this branch? This cannot be undone.')
    : await confirmInSheet({ title: 'Discard all changes?', body: 'This wipes every uncommitted change on this branch and cannot be undone.', confirmLabel: 'Discard all', danger: true });
  if (!ok) return;
  await runSourceAction('discard', 'git/discard', { body: JSON.stringify({}) }, { success: 'Changes discarded.', failure: 'Discard failed.' });
}

async function discardFile(path) {
  if (!path) return;
  if (!sourceCtl.status?.worktree) {
    setSourceFeedback('err', 'Discard is only available for worktree sessions — it would wipe uncommitted changes in your primary checkout.');
    return;
  }
  if (!confirm(`Discard changes to ${path}? This cannot be undone.`)) return;
  await runSourceAction('discard', 'git/discard', { body: JSON.stringify({ paths: [path] }) }, { success: `Discarded ${path}.`, failure: 'Discard failed.' });
}

// ── Compare-mode pills (branch / worktree / log) ─────────────────────────
function renderCompareModes() {
  const nav = getMount()?.querySelector('#dr-compare');
  if (!nav) return;
  const modes = [
    { key: 'branch', label: () => `${diffState.refs.branch.base} → ${diffState.refs.branch.head}` },
    { key: 'worktree', label: () => 'HEAD → working tree' },
    { key: 'log', label: () => 'log' },
  ];
  const onBase = sourceCtl.status?.branch && sourceCtl.status?.defaultBranch
    && sourceCtl.status.branch === sourceCtl.status.defaultBranch;
  nav.innerHTML = modes.map((m) => {
    if (m.key === 'branch' && onBase) return '';
    return `<button class="dr-compare-pill${diffState.mode === m.key ? ' dr-compare-active' : ''}"
      data-mode="${m.key}" role="tab" type="button">${escapeHtml(m.label())}</button>`;
  }).join('');
  for (const btn of nav.querySelectorAll('.dr-compare-pill')) {
    btn.addEventListener('click', () => switchCompareMode(btn.dataset.mode));
  }
}

function switchCompareMode(mode) {
  if (diffState.mode === mode) return;
  diffState.mode = mode;
  renderCompareModes();
  diffState.comments.clear();
  diffState.openDraftKey = null;
  diffState.draftRange = null;
  diffState.collapsed.clear();
  clearDiffSendWarning();
  const logEl = getMount().querySelector('#dr-log');
  const viewport = getMount().querySelector('#dr-viewport');
  if (mode === 'log') {
    logEl.hidden = false;
    viewport.hidden = true;
    renderSourceLog();
    renderHeaderStats();
    return;
  }
  logEl.hidden = true;
  viewport.hidden = false;
  fetchAndRenderDiff();
}

// ── Diff fetch + render ───────────────────────────────────────────────────
async function fetchAndRenderDiff() {
  const sessionId = diffState.ctx?.sessionId;
  if (!sessionId) return;
  const viewport = getMount()?.querySelector('#dr-viewport');
  const list = getMount()?.querySelector('#dr-files-list');
  if (!viewport || !list) return;
  viewport.textContent = 'Loading…';
  list.innerHTML = '';

  let payload;
  try {
    const r = await fetch(`/api/sessions/${encodeURIComponent(sessionId)}/diff?mode=${diffState.mode}`);
    if (!r.ok) throw new Error(`HTTP ${r.status}`);
    payload = await r.json();
  } catch (err) {
    viewport.textContent = `Failed to load diff: ${err.message}`;
    return;
  }
  if (diffState.mode === 'branch') {
    diffState.refs.branch = {
      base: diffRefLabel(payload.baseRef),
      head: diffRefLabel(payload.headRef),
    };
  }
  renderCompareModes();

  if (payload.onBaseBranch && diffState.mode === 'branch') {
    diffState.mode = 'worktree';
    return fetchAndRenderDiff();
  }
  diffState.fullFiles.clear();
  diffState.openDraftKey = null;
  diffState.draftRange = null;
  // Bytewise, as git orders tracked files; untracked ones arrive appended and would break the rail's tree order.
  diffState.files = (payload.files || []).sort((a, b) => (a.path < b.path ? -1 : a.path > b.path ? 1 : 0));
  renderDiffFileList();
  renderDiffContent();
  renderHeaderStats();
  renderFooter();
  applyStagedStateToCards();
}

function diffRefLabel(s) { return s === 'WORKTREE' ? 'working tree' : (s || '—'); }

function renderHeaderStats() {
  const el = getMount()?.querySelector('#dr-hdr-stats');
  if (!el) return;
  const files = diffState.files;
  let add = 0; let del = 0;
  for (const f of files) for (const h of f.hunks ?? []) for (const r of h.rows ?? []) {
    if (r.op === '+') add++; else if (r.op === '-') del++;
  }
  const s = sourceCtl.status;
  const branch = s?.branch ? `<span class="o-ref">branch:</span> <span class="o-pill code">${escapeHtml(s.branch)}</span>` : '';
  el.innerHTML = diffState.mode === 'log'
    ? `${sourceCtl.log.length} commit${sourceCtl.log.length === 1 ? '' : 's'}`
    : `${files.length} file${files.length === 1 ? '' : 's'}`
      + ` <span class="dr-stat-add">+${add}</span> <span class="dr-stat-del">−${del}</span>`
      + (branch ? ` <span class="dr-hdr-sep">·</span> ${branch}` : '');
}

function renderDiffFileList() {
  const list = getMount()?.querySelector('#dr-files-list');
  const hdr = getMount()?.querySelector('#dr-files-hdr');
  const filesNav = getMount()?.querySelector('.dr-files');
  if (!list || !hdr) return;
  const q = diffState.filter.trim().toLowerCase();
  const files = q ? diffState.files.filter((f) => f.path.toLowerCase().includes(q)) : diffState.files;
  hdr.innerHTML = `<span>${diffState.files.length} file${diffState.files.length === 1 ? '' : 's'} changed</span>`
    + '<span class="dr-files-caret" aria-hidden="true"></span>';
  filesNav?.classList.toggle('dr-files-open', filesStripOpen);
  if (files.length === 0) {
    list.innerHTML = `<div class="dr-empty">${diffState.files.length === 0 ? 'No changes.' : 'No files match.'}</div>`;
    return;
  }
  const rows = [];
  const walk = (nodes) => {
    for (const n of nodes) {
      if (n.kind === 'file') { rows.push(fileRowHtml(n)); continue; }
      const open = Boolean(q) || !diffState.collapsedDirs.has(n.path);
      rows.push(dirRowHtml(n, open, Boolean(q)));
      if (open) walk(n.children);
    }
  };
  walk(buildFileTree(files));
  list.innerHTML = rows.join('');
  for (const el of list.querySelectorAll('.dr-dir-row')) onActivate(el, () => toggleDir(el.dataset.dir));
  for (const el of list.querySelectorAll('.dr-file-row')) {
    onActivate(el, () => {
      const path = el.dataset.file;
      if (diffState.collapsed.has(path)) {
        diffState.collapsed.delete(path);
        getMount().querySelector(`.dr-file-card[data-file="${cssEscape(path)}"]`)?.classList.remove('is-collapsed');
      }
      getMount().querySelector(`.dr-file-card[data-file="${cssEscape(path)}"]`)
        ?.scrollIntoView({ block: 'start', behavior: 'smooth' });
    });
  }
  updateDiffCommentBadges();
}

function onActivate(el, fn) {
  el.addEventListener('click', fn);
  el.addEventListener('keydown', (e) => {
    if (e.key !== 'Enter' && e.key !== ' ') return;
    e.preventDefault();
    fn();
  });
}

function toggleDir(path) {
  if (diffState.filter.trim()) return;
  if (diffState.collapsedDirs.has(path)) diffState.collapsedDirs.delete(path);
  else diffState.collapsedDirs.add(path);
  renderDiffFileList();
  getMount()?.querySelector(`.dr-dir-row[data-dir="${cssEscape(path)}"]`)?.focus();
}

// While filtering every directory is forced open, so its toggle is shown as disabled rather than silently ignored.
function dirRowHtml(n, open, filtering) {
  const toggle = filtering ? 'aria-disabled="true"' : 'tabindex="0"';
  return `<div class="dr-dir-row" data-dir="${escapeHtml(n.path)}" style="--depth:${n.depth}" title="${escapeHtml(n.path)}/" role="button" ${toggle} aria-expanded="${open}">
    <span class="dr-dir-caret" aria-hidden="true"></span>
    <span class="dr-dir-name">${escapeHtml(n.name)}/</span>
    <span class="dr-file-stats">${statsHtml(n.add, n.del)}</span>
    <span class="dr-file-comments" data-dir-badge="${escapeHtml(n.path)}" hidden>0</span>
  </div>`;
}

function fileRowHtml(n) {
  const f = n.file;
  const dotClass = f.untracked ? 'new' : (f.status === 'deleted' ? 'deleted' : f.status === 'added' ? 'new' : 'modified');
  return `<div class="dr-file-row" data-file="${escapeHtml(f.path)}" style="--depth:${n.depth}" title="${escapeHtml(f.path)}" role="button" tabindex="0">
    <span class="dr-dot ${dotClass}"></span>
    <span class="dr-file-name">${escapeHtml(n.name)}</span>
    <span class="dr-file-stats">${statsHtml(n.add, n.del)}</span>
    <span class="dr-file-comments" data-file-badge="${escapeHtml(f.path)}" hidden>0</span>
  </div>`;
}

function statsHtml(add, del) {
  const bits = [];
  if (add) bits.push(`<span class="dr-stat-add">+${add}</span>`);
  if (del) bits.push(`<span class="dr-stat-del">−${del}</span>`);
  return bits.join(' ');
}

function renderDiffContent() {
  const content = getMount()?.querySelector('#dr-viewport');
  if (!content) return;
  if (diffState.files.length === 0) {
    content.innerHTML = '<div class="dr-empty">No changes in this view.</div>';
    return;
  }
  const mobile = !isDesktop();
  content.innerHTML = diffState.files.map((f) => renderDiffFileHtml(f, mobile)).join('');
}

function renderDiffFileHtml(f, isMobile) {
  const renameNote = f.oldPath ? ` <span class="dr-file-renamed">(was ${escapeHtml(f.oldPath)})</span>` : '';
  const truncNote = f.truncated ? ' <span class="dr-file-truncated">(truncated — view in terminal)</span>' : '';
  const untrackedNote = f.untracked ? ' <span class="dr-file-untracked">(untracked)</span>' : '';
  const statusKey = f.untracked ? 'untracked' : f.status;
  const icon = f.untracked ? '?' : (DIFF_STATUS_ICON[f.status] ?? '?');
  const status = `<span class="dr-file-card-status" data-status="${escapeHtml(statusKey)}">${icon}</span>`;
  const stageable = diffState.mode === 'worktree';
  const staged = stageable && isFileStaged(f.path);
  const stageBox = stageable
    ? `<label class="dr-file-stage" title="Stage this file for commit">
         <span>Stage</span>
         <input type="checkbox" data-file="${escapeHtml(f.path)}" ${staged ? 'checked' : ''}>
       </label>`
    : '';
  const discardBtn = stageable && sourceCtl.status?.worktree
    ? `<button class="dr-file-discard" type="button" data-discard="${escapeHtml(f.path)}"
         title="Discard changes to this file (cannot be undone)">Discard</button>`
    : '';
  const head = `<div class="dr-file-card-head" role="button" tabindex="0" aria-label="Toggle ${escapeHtml(f.path)}">
    <span class="dr-file-card-caret" aria-hidden="true"></span>
    ${status}
    <span class="dr-file-card-name">${escapeHtml(f.path)}${renameNote}${truncNote}${untrackedNote}</span>
    ${discardBtn}
    ${stageBox}
  </div>`;
  // New files show their contents like any added file (backend synthesizes the
  // hunks via `git diff --no-index`), so don't auto-collapse them — the whole point
  // is to read a new file before approving. Only staged/explicitly-collapsed hide.
  const collapsedNow = diffState.collapsed.has(f.path) || (stageable && staged);
  const cls = `dr-file-card${collapsedNow ? ' is-collapsed' : ''}${staged ? ' is-staged' : ''}${f.untracked ? ' is-untracked' : ''}`;
  if (f.binary) {
    return `<section class="${cls}" data-file="${escapeHtml(f.path)}">${head}<div class="dr-binary">Binary file${f.untracked ? ' (new)' : ' changed'}.</div></section>`;
  }
  if (!f.hunks || f.hunks.length === 0) {
    const note = f.untracked
      ? 'New empty file — check Stage to include it in the next commit.'
      : 'No changes.';
    return `<section class="${cls}" data-file="${escapeHtml(f.path)}">${head}<div class="dr-untracked-note">${note}</div></section>`;
  }
  const gaps = isExpandable(f) ? gapsFor(f.hunks) : [];
  const parts = f.hunks.map((h, i) => {
    const gap = gaps.find((g) => g.at === i);
    // The bar carries this hunk's @@ line, so rows revealed upward never land beneath a header that no longer describes them.
    return gap
      ? gapBarHtml(f, gap, h) + renderRowsHtml(f.path, h.rows, isMobile)
      : renderDiffHunkHtml(f.path, h, isMobile);
  });
  const trailing = gaps.find((g) => g.at === f.hunks.length);
  if (trailing) parts.push(gapBarHtml(f, trailing, null));
  return `<section class="${cls}" data-file="${escapeHtml(f.path)}">${head}${parts.join('')}</section>`;
}

// Added, deleted and untracked files already show every line, so there is nothing to expand.
function isExpandable(f) {
  return !f.binary && !f.untracked && !f.truncated && f.hunks.length > 0
    && (f.status === 'modified' || f.status === 'renamed' || f.status === 'copied');
}

const EXPAND_STEP = 20;
const SHOW_ALL_MAX = 200;

function hunkHeaderText(h) {
  return `@@ -${h.oldStart},${h.oldLines} +${h.newStart},${h.newLines} @@`;
}

function hunkAttrs(h) {
  return `data-old-start="${h.oldStart}" data-old-lines="${h.oldLines}" data-new-start="${h.newStart}" data-new-lines="${h.newLines}"`;
}

function gapBarHtml(f, gap, hunk) {
  const kind = gap.at === 0 ? 'lead' : gap.to === null ? 'trail' : 'mid';
  const oldPath = f.oldPath ? ` data-old-path="${escapeHtml(f.oldPath)}"` : '';
  const header = hunk ? hunkHeaderText(hunk) : '';
  return `<div class="dr-gap" tabindex="-1" data-file="${escapeHtml(f.path)}"${oldPath} data-gap="${kind}" data-header="${escapeHtml(header)}"
    ${hunk ? hunkAttrs(hunk) : ''} data-from="${gap.from}" data-to="${gap.to ?? ''}">${gapBarInnerHtml(kind, gap.from, gap.to, header)}</div>`;
}

// Revealed context joins a hunk, so that hunk's @@ line must widen to keep describing the rows beneath it.
function adjustHunkHeader(el, { shift = 0, oldLines = 0, newLines = 0 }) {
  if (!el) return;
  const d = el.dataset;
  const h = {
    oldStart: Number(d.oldStart) - shift,
    oldLines: Number(d.oldLines) + oldLines,
    newStart: Number(d.newStart) - shift,
    newLines: Number(d.newLines) + newLines,
  };
  Object.assign(d, { oldStart: h.oldStart, oldLines: h.oldLines, newStart: h.newStart, newLines: h.newLines });
  const text = hunkHeaderText(h);
  if (el.classList.contains('dr-gap')) {
    d.header = text;
    const span = el.querySelector('.dr-gap-hdr');
    if (span) span.textContent = text;
  } else {
    el.textContent = text;
  }
}

function previousHunkHeader(bar) {
  for (let el = bar.previousElementSibling; el; el = el.previousElementSibling) {
    if (el.matches('.dr-hunk-hdr, .dr-gap[data-new-start]')) return el;
  }
  return null;
}

function gapBarInnerHtml(kind, from, to, header, note = '') {
  const hidden = to === null ? null : to - from + 1;
  const btn = (dir, label, aria) =>
    `<button type="button" class="o-btn o-btn--ghost sm dr-gap-btn" data-expand="${dir}" aria-label="${aria}">${label}</button>`;
  const buttons = [];
  if (kind !== 'trail') buttons.push(btn('up', `↑ Expand ${EXPAND_STEP}`, `Show ${EXPAND_STEP} more lines above`));
  if (kind !== 'lead') buttons.push(btn('down', `↓ Expand ${EXPAND_STEP}`, `Show ${EXPAND_STEP} more lines below`));
  if (hidden !== null && hidden <= SHOW_ALL_MAX) buttons.push(btn('all', 'Show all', `Show all ${hidden} hidden lines`));
  const hdr = header ? `<span class="dr-gap-hdr">${escapeHtml(header)}</span>` : '';
  const noteHtml = note ? `<span class="dr-gap-note is-error" role="status">${note}</span>` : '';
  const count = hidden === null ? '' : `<span class="dr-gap-count">${hidden} hidden line${hidden === 1 ? '' : 's'}</span>`;
  return hdr + buttons.join('') + noteHtml + count;
}

function loadFullFile(path, oldPath) {
  const key = `${diffState.mode}:${path}`;
  let pending = diffState.fullFiles.get(key);
  if (pending) return pending;
  const qs = new URLSearchParams({ mode: diffState.mode, path });
  if (oldPath) qs.set('oldPath', oldPath);
  pending = fetch(`/api/sessions/${encodeURIComponent(diffState.ctx.sessionId)}/diff/file?${qs}`)
    .then((r) => (r.ok ? r.json() : null))
    .then((body) => body?.file ?? null)
    .catch(() => null)
    .then((file) => {
      if (!file) diffState.fullFiles.delete(key);
      return file;
    });
  diffState.fullFiles.set(key, pending);
  return pending;
}

// Inserts only the revealed rows next to the bar — the rest of the viewport is never repainted.
async function expandGap(btn) {
  const bar = btn.closest('.dr-gap');
  const { file, oldPath, gap: kind } = bar.dataset;
  const pressed = btn.dataset.expand;
  // Show all on a leading gap reveals rows above its hunk, which is the upward case.
  const dir = pressed === 'all' && kind === 'lead' ? 'up' : pressed;
  let from = Number(bar.dataset.from);
  let to = bar.dataset.to === '' ? null : Number(bar.dataset.to);
  for (const b of bar.querySelectorAll('.dr-gap-btn')) b.disabled = true;
  const full = await loadFullFile(file, oldPath);
  if (!bar.isConnected) return;
  if (!full) {
    bar.innerHTML = gapBarInnerHtml(kind, from, to, bar.dataset.header, 'Couldn\'t load more context');
    refocusGap(bar, pressed);
    return;
  }
  const loaded = lastNewLine(full);
  if (to === null) to = loaded;
  const [a, b] = pressed === 'all' ? [from, to]
    : dir === 'up' ? [Math.max(from, to - EXPAND_STEP + 1), to]
    : [from, Math.min(to, from + EXPAND_STEP - 1)];
  // Rows past a truncated load aren't contiguous with the hunk below, so nothing can be shown above it.
  if (full.truncated && dir === 'up' && to > loaded) {
    showRestNotLoaded(bar);
    return;
  }
  const rows = gapRows(full, a, Math.min(b, loaded));
  bar.insertAdjacentHTML(dir === 'up' ? 'afterend' : 'beforebegin', renderRowsHtml(file, rows, !isDesktop(), ' dr-expanded'));
  const grown = { oldLines: rows.length, newLines: rows.length };
  if (dir === 'up') adjustHunkHeader(bar.dataset.header ? bar : null, { ...grown, shift: rows.length });
  else adjustHunkHeader(previousHunkHeader(bar), grown);
  if (full.truncated && b >= loaded) {
    showRestNotLoaded(bar);
    return;
  }
  if (dir === 'up') to = a - 1; else from = b + 1;
  if (from > to) {
    closeGap(bar);
    return;
  }
  bar.dataset.from = String(from);
  bar.dataset.to = String(to);
  bar.innerHTML = gapBarInnerHtml(kind, from, to, bar.dataset.header);
  refocusGap(bar, pressed);
}

function showRestNotLoaded(bar) {
  const header = bar.dataset.header;
  bar.innerHTML = (header ? `<span class="dr-gap-hdr">${escapeHtml(header)}</span>` : '')
    + '<span class="dr-gap-note" role="status">Rest of file not loaded</span>';
  bar.focus({ preventScroll: true });
}

// Nothing hidden is left between the two hunks, so they become one; a leading gap has no hunk above and keeps its own header.
function closeGap(bar) {
  const d = bar.dataset;
  const prev = previousHunkHeader(bar);
  let focusTarget = prev;
  if (d.header && prev) {
    adjustHunkHeader(prev, { oldLines: Number(d.oldLines), newLines: Number(d.newLines) });
    bar.remove();
  } else if (d.header) {
    const hdr = document.createElement('div');
    hdr.className = 'dr-hunk-hdr';
    hdr.tabIndex = -1;
    Object.assign(hdr.dataset, { oldStart: d.oldStart, oldLines: d.oldLines, newStart: d.newStart, newLines: d.newLines });
    hdr.textContent = d.header;
    bar.replaceWith(hdr);
    focusTarget = hdr;
  } else {
    const card = bar.closest('.dr-file-card');
    bar.remove();
    focusTarget ??= card.querySelector('.dr-file-card-head');
  }
  focusTarget?.focus({ preventScroll: true });
}

function refocusGap(bar, dir) {
  (bar.querySelector(`.dr-gap-btn[data-expand="${dir}"]`) ?? bar.querySelector('.dr-gap-btn'))?.focus();
}

function isFileStaged(path) {
  if (!sourceCtl.status?.files) return false;
  const f = sourceCtl.status.files.find((x) => x.path === path);
  return Boolean(f) && f.index !== '.' && f.index !== ' ' && f.index !== '?' && f.index !== '!';
}

function applyStagedStateToCards() {
  if (diffState.mode !== 'worktree') return;
  for (const card of getMount()?.querySelectorAll('#dr-viewport .dr-file-card') ?? []) {
    const path = card.dataset.file;
    if (!path) continue;
    const staged = isFileStaged(path);
    const cb = card.querySelector('.dr-file-stage input');
    if (cb) cb.checked = staged;
    card.classList.toggle('is-staged', staged);
    if (staged) { diffState.collapsed.add(path); card.classList.add('is-collapsed'); }
  }
}

// Queued in click order so stage/unstage requests for the same session land in
// the order the user toggled them. `sessionId` is captured synchronously at
// click time (not re-read from the live diffState.ctx singleton at dequeue
// time) so a queued action still targets the worktree it was meant for even if
// the overlay has since been reopened for a different session.
let stageQueue = Promise.resolve();
function stageFileFromUi(sessionId, path, action) {
  stageQueue = stageQueue.then(() => stageFileImpl(sessionId, path, action)).catch(() => {});
}

async function stageFileImpl(sessionId, path, action) {
  if (!sessionId) return;
  try {
    const r = await fetch(`/api/sessions/${encodeURIComponent(sessionId)}/git/stage`, {
      method: 'POST',
      headers: { 'content-type': 'application/json' },
      body: JSON.stringify({ paths: [path], action }),
    });
    const body = await r.json().catch(() => null);
    if (diffState.ctx?.sessionId !== sessionId) return; // overlay moved to a different session — drop stale result
    if (body?.status) sourceCtl.status = body.status;
    if (!r.ok || !body?.ok) {
      const detail = body
        ? [body.stderr, body.stdout].filter((s) => s && s.trim().length > 0).join('\n').trim() || body.error
        : `HTTP ${r.status}`;
      setSourceFeedback('err', action === 'stage' ? 'Stage failed.' : 'Unstage failed.', detail || null);
    }
  } catch (err) {
    if (diffState.ctx?.sessionId !== sessionId) return;
    setSourceFeedback('err', `${action === 'stage' ? 'Stage' : 'Unstage'} failed.`, String(err.message ?? err));
  } finally {
    if (diffState.ctx?.sessionId === sessionId) {
      applyStagedStateToCards();
      renderFooter();
    }
  }
}

function renderDiffHunkHtml(filePath, h, isMobile) {
  return `<div class="dr-hunk-hdr" tabindex="-1" ${hunkAttrs(h)}>${hunkHeaderText(h)}</div>` + renderRowsHtml(filePath, h.rows, isMobile);
}

function renderRowsHtml(filePath, rows, isMobile, extraCls = '') {
  if (isMobile) {
    return `<div class="dr-hunk-unified${extraCls}">${rows.map((r) => renderUnifiedRowHtml(filePath, r)).join('')}</div>`;
  }
  const left = []; const right = [];
  let i = 0;
  while (i < rows.length) {
    const r = rows[i];
    if (r.op === ' ') {
      left.push(renderSplitRowHtml(filePath, 'old', ' ', r.content, r.oldLine));
      right.push(renderSplitRowHtml(filePath, 'new', ' ', r.content, r.newLine));
      i++; continue;
    }
    const dels = [];
    while (i < rows.length && rows[i].op === '-') { dels.push(rows[i]); i++; }
    const adds = [];
    while (i < rows.length && rows[i].op === '+') { adds.push(rows[i]); i++; }
    for (let k = 0; k < Math.max(dels.length, adds.length); k++) {
      const d = dels[k]; const a = adds[k];
      left.push(d ? renderSplitRowHtml(filePath, 'old', '-', d.content, d.oldLine) : '<div class="dr-row dr-row-empty"></div>');
      right.push(a ? renderSplitRowHtml(filePath, 'new', '+', a.content, a.newLine) : '<div class="dr-row dr-row-empty"></div>');
    }
  }
  return `<div class="dr-hunk-split${extraCls}"><div>${left.join('')}</div><div>${right.join('')}</div></div>`;
}

function renderUnifiedRowHtml(filePath, r) {
  const cls = r.op === '+' ? 'dr-add' : r.op === '-' ? 'dr-del' : 'dr-ctx';
  const side = r.op === '-' ? 'old' : 'new';
  const line = r.op === '-' ? r.oldLine : r.newLine;
  const key = diffCommentKey(filePath, side, line);
  return `<div class="dr-row dr-line ${cls}" data-file="${escapeHtml(filePath)}" data-side="${side}" data-line="${line}" data-key="${escapeHtml(key)}">
    <span class="dr-mark">${r.op}</span><span class="dr-code">${escapeHtml(r.content)}</span>
  </div>`;
}

function renderSplitRowHtml(filePath, side, mark, content, line) {
  const cls = mark === '+' ? 'dr-add' : mark === '-' ? 'dr-del' : 'dr-ctx';
  const key = diffCommentKey(filePath, side, line);
  return `<div class="dr-row dr-line ${cls}" data-file="${escapeHtml(filePath)}" data-side="${side}" data-line="${line}" data-key="${escapeHtml(key)}">
    <span class="dr-mark">${mark}</span><span class="dr-code">${escapeHtml(content)}</span>
  </div>`;
}

// ── Per-hunk comments ─────────────────────────────────────────────────────
function activeCommentCount() { return diffState.comments.size; }

function onDiffContentClick(e) {
  if (e.target.closest('.dr-comment-card') || e.target.closest('.dr-comment-form')) return;
  if (e.target.closest('.dr-file-stage')) return;
  const gapBtn = e.target.closest('.dr-gap-btn');
  if (gapBtn) { void expandGap(gapBtn); return; }
  const discardBtn = e.target.closest('.dr-file-discard');
  if (discardBtn) { void discardFile(discardBtn.dataset.discard); return; }
  const head = e.target.closest('.dr-file-card-head');
  if (head) {
    const card = head.closest('.dr-file-card');
    const path = card?.dataset.file;
    if (!path) return;
    if (diffState.collapsed.has(path)) { diffState.collapsed.delete(path); card.classList.remove('is-collapsed'); }
    else { diffState.collapsed.add(path); card.classList.add('is-collapsed'); }
    return;
  }
  const row = e.target.closest('.dr-row');
  if (!row || row.classList.contains('dr-row-empty')) return;
  if (diffState.draftRange && (e.shiftKey || diffState.draftRange.selecting)) { extendDraftTo(row); return; }
  openCommentFromRow(row);
}

function openCommentFromRow(row) {
  const file = row.dataset.file;
  const side = row.dataset.side === 'old' ? 'old' : 'new';
  const line = Number(row.dataset.line);
  if (!file || !line) return;
  const key = diffCommentKey(file, side, line);
  if (diffState.openDraftKey && diffState.openDraftKey !== key) return; // one draft open at a time
  if (row.nextElementSibling?.classList.contains('dr-comment-card')) row.nextElementSibling.remove();
  const existing = diffState.comments.get(key);
  openDiffCommentForm(row, {
    file, side, start: existing?.startLine ?? line, end: line,
    content: existing?.content ?? '', editingKey: existing ? key : null,
  });
}

function openDiffCommentForm(row, { file, side, start, end, anchor = start, content = '', editingKey = null }) {
  if (row.nextElementSibling?.classList.contains('dr-comment-form')) return;
  const key = diffCommentKey(file, side, end);
  const form = document.createElement('form');
  form.className = 'dr-comment-form';
  const rangeLabel = document.createElement('div');
  rangeLabel.className = 'dr-comment-range';
  rangeLabel.textContent = `Lines ${start}–${end}`;
  rangeLabel.hidden = start === end;
  const ta = document.createElement('textarea');
  ta.placeholder = 'Leave a comment…';
  ta.value = content;
  const actions = document.createElement('div');
  actions.className = 'dr-comment-form-actions';
  const rangeToggle = document.createElement('button');
  rangeToggle.type = 'button'; rangeToggle.textContent = 'Select range';
  rangeToggle.className = 'o-btn o-btn--ghost sm dr-comment-range-toggle';
  rangeToggle.setAttribute('aria-pressed', 'false');
  const cancel = document.createElement('button');
  cancel.type = 'button'; cancel.textContent = 'Cancel'; cancel.className = 'o-btn o-btn--ghost sm dr-comment-cancel';
  const save = document.createElement('button');
  save.type = 'submit'; save.textContent = 'Save'; save.className = 'o-btn o-btn--default sm';
  actions.append(rangeToggle, cancel, save);
  const hint = document.createElement('div');
  hint.className = 'dr-comment-range-hint';
  hint.setAttribute('aria-live', 'polite');
  hint.hidden = true;
  form.append(rangeLabel, ta, hint, actions);
  row.insertAdjacentElement('afterend', form);
  diffState.openDraftKey = key;
  diffState.draftRange = { file, side, anchor, start, end, editingKey, selecting: false };
  paintRange(rowBlock(row), file, side, start, end, 'dr-row--in-range');
  const editing = editingKey && diffState.comments.get(editingKey);
  if (editing?.startLine) {
    for (const r of rangeRows(rowBlock(row), file, side, editing.startLine, editing.line)) r.classList.remove('dr-row--commented');
  }
  ta.focus();

  ta.addEventListener('keydown', (ev) => {
    if ((ev.metaKey || ev.ctrlKey) && ev.key === 'Enter') { ev.preventDefault(); form.requestSubmit(); }
  });
  rangeToggle.addEventListener('click', () => setRangeSelecting(form, !diffState.draftRange.selecting));
  cancel.addEventListener('click', () => {
    closeDraft(form);
    const original = editingKey && findRowByKey(editingKey);
    if (original) renderDiffCommentChip(original, editingKey);
    repaintCommented(file);
  });
  form.addEventListener('submit', (ev) => {
    ev.preventDefault();
    const text = ta.value.trim();
    if (!text) return;
    const lineText = codeText(row);
    const comment = start === end
      ? { file, side, line: end, content: text, lineText }
      : {
        file, side, line: end, startLine: start, content: text, lineText,
        quote: rangeRows(rowBlock(row), file, side, start, end)
          .map((r) => ({ mark: r.querySelector('.dr-mark')?.textContent ?? '', text: codeText(r) })),
      };
    if (editingKey && editingKey !== key) diffState.comments.delete(editingKey);
    diffState.comments.set(key, comment);
    closeDraft(form);
    renderDiffCommentChip(row, key);
    repaintCommented(file);
    updateDiffCommentBadges();
    renderHeaderStats();
    renderFooter();
    clearDiffSendWarning();
  });
}

function closeDraft(form) {
  form.remove();
  for (const r of getMount()?.querySelectorAll('.dr-row--in-range') ?? []) r.classList.remove('dr-row--in-range');
  diffState.openDraftKey = null;
  diffState.draftRange = null;
}

// Re-opens the draft on the range's new end row, keeping whatever was typed.
function extendDraftTo(row) {
  const d = diffState.draftRange;
  const form = getMount()?.querySelector('.dr-comment-form');
  if (!d || !form) return;
  const anchorRow = findRowByKey(diffCommentKey(d.file, d.side, d.anchor));
  if (row.dataset.file !== d.file || row.dataset.side !== d.side || !anchorRow || rowBlock(row) !== rowBlock(anchorRow)) {
    showRangeHint(form, 'Ranges stay within one hunk, on one side.');
    return;
  }
  const line = Number(row.dataset.line);
  const start = Math.min(d.anchor, line);
  const end = Math.max(d.anchor, line);
  const key = diffCommentKey(d.file, d.side, end);
  if (key !== d.editingKey && diffState.comments.has(key)) {
    showRangeHint(form, 'A comment already ends on that line.');
    return;
  }
  const content = form.querySelector('textarea').value;
  const { file, side, anchor, editingKey } = d;
  closeDraft(form);
  openDiffCommentForm(findRowByKey(key), { file, side, start, end, anchor, content, editingKey });
}

function setRangeSelecting(form, on) {
  diffState.draftRange.selecting = on;
  form.querySelector('.dr-comment-range-toggle').setAttribute('aria-pressed', String(on));
  const hint = form.querySelector('.dr-comment-range-hint');
  if (on) showRangeHint(form, `${isDesktop() ? 'Click' : 'Tap'} the line the range should end on.`, false);
  else hint.hidden = true;
}

function showRangeHint(form, text, refusal = true) {
  const hint = form.querySelector('.dr-comment-range-hint');
  hint.textContent = text;
  hint.classList.toggle('is-refusal', refusal);
  hint.hidden = false;
}

function findRowByKey(key) {
  return getMount()?.querySelector(`.dr-row[data-key="${cssEscape(key)}"]`) ?? null;
}

function rowBlock(row) { return row.closest('.dr-hunk-split, .dr-hunk-unified'); }

function codeText(row) { return row.querySelector('.dr-code')?.textContent ?? ''; }

function rangeRows(block, file, side, start, end) {
  return [...block.querySelectorAll(`.dr-row[data-side="${side}"]`)].filter((r) => {
    const line = Number(r.dataset.line);
    return r.dataset.file === file && line >= start && line <= end;
  });
}

function paintRange(block, file, side, start, end, cls) {
  if (start === end) return;
  for (const r of rangeRows(block, file, side, start, end)) r.classList.add(cls);
}

function repaintCommented(file) {
  const card = getMount()?.querySelector(`.dr-file-card[data-file="${cssEscape(file)}"]`);
  if (!card) return;
  for (const r of card.querySelectorAll('.dr-row--commented')) r.classList.remove('dr-row--commented');
  for (const c of diffState.comments.values()) {
    if (c.file !== file || !c.startLine) continue;
    const endRow = findRowByKey(diffCommentKey(c.file, c.side, c.line));
    if (endRow) paintRange(rowBlock(endRow), c.file, c.side, c.startLine, c.line, 'dr-row--commented');
  }
}

function renderDiffCommentChip(row, key) {
  if (row.nextElementSibling?.classList.contains('dr-comment-card') && row.nextElementSibling.dataset.key === key) {
    row.nextElementSibling.remove();
  }
  const c = diffState.comments.get(key);
  if (!c) return;
  const chip = document.createElement('div');
  chip.className = 'dr-comment-card';
  chip.dataset.key = key;
  const body = document.createElement('div');
  body.className = 'dr-comment-content';
  body.textContent = c.content;
  const actions = document.createElement('div');
  actions.className = 'dr-comment-actions';
  const editBtn = document.createElement('button'); editBtn.type = 'button'; editBtn.textContent = 'Edit'; editBtn.className = 'dr-comment-link';
  const delBtn = document.createElement('button'); delBtn.type = 'button'; delBtn.textContent = 'Delete'; delBtn.className = 'dr-comment-link dr-comment-link--danger';
  actions.append(editBtn, delBtn);
  if (c.startLine) {
    const range = document.createElement('div');
    range.className = 'dr-comment-range';
    range.textContent = `Lines ${c.startLine}–${c.line}`;
    chip.append(range);
  }
  chip.append(body, actions);
  row.insertAdjacentElement('afterend', chip);

  delBtn.addEventListener('click', () => {
    diffState.comments.delete(key);
    chip.remove();
    repaintCommented(c.file);
    updateDiffCommentBadges();
    renderHeaderStats();
    renderFooter();
  });
  editBtn.addEventListener('click', () => {
    const openForm = getMount().querySelector('.dr-comment-form');
    if (openForm) {
      openForm.scrollIntoView({ block: 'center', behavior: 'smooth' });
      openForm.querySelector('textarea')?.focus({ preventScroll: true });
      return;
    }
    chip.remove();
    openDiffCommentForm(row, {
      file: c.file, side: c.side, start: c.startLine ?? c.line, end: c.line, content: c.content, editingKey: key,
    });
  });
}

function updateDiffCommentBadges() {
  const counts = new Map();
  for (const c of diffState.comments.values()) counts.set(c.file, (counts.get(c.file) ?? 0) + 1);
  for (const badge of getMount()?.querySelectorAll('[data-file-badge]') ?? []) {
    setBadge(badge, counts.get(badge.getAttribute('data-file-badge')) ?? 0);
  }
  // An open directory's files show their own badges, so only a collapsed one stands in for them.
  for (const badge of getMount()?.querySelectorAll('[data-dir-badge]') ?? []) {
    const prefix = `${badge.getAttribute('data-dir-badge')}/`;
    let n = 0;
    if (badge.closest('.dr-dir-row')?.getAttribute('aria-expanded') === 'false') {
      for (const [file, c] of counts) if (file.startsWith(prefix)) n += c;
    }
    setBadge(badge, n);
  }
}

function setBadge(badge, n) {
  badge.textContent = String(n);
  badge.hidden = n === 0;
}

function formatDiffReviewMessage() {
  const sorted = [...diffState.comments.values()]
    .sort((a, b) => (a.file !== b.file ? (a.file < b.file ? -1 : 1) : (a.startLine ?? a.line) - (b.startLine ?? b.line)));
  return formatDiffReviewMessageShared(sorted);
}

function setDiffSendWarning(text) {
  const w = getMount()?.querySelector('#dr-warning');
  if (!w) return;
  w.hidden = false;
  w.textContent = text;
}
function clearDiffSendWarning() {
  const w = getMount()?.querySelector('#dr-warning');
  if (!w) return;
  w.hidden = true;
  w.textContent = '';
}

// The live step behind the open overlay, when it's a controller-owned one that can
// still take a turn. Re-read from the store rather than trusting diffState.ctx.step,
// which is a snapshot from the moment the overlay opened.
function liveOrchestratedStep() {
  const { jobId, stepId } = diffState.ctx ?? {};
  if (!jobId || !stepId) return null;
  const step = work.get().byId.get(jobId)?.steps?.find((s) => s.id === stepId);
  if (!step || step.type !== 'orchestrated') return null;
  if (step.cancelled || step.state === 'resolved' || step.state === 'failed') return null;
  return step;
}

// "Request changes" — drafted per-hunk comments flow back as a single structured
// review message. For a controller-owned step it must go through the step's inbox
// (that's what clears `waitingOn` and gives the controller its turn back); a raw WS
// message into its session would prompt it out of band and leave the step parked.
// Every other session takes the chat path, via /git/review for validation.
async function submitReview() {
  if (diffState.openDraftKey) {
    setDiffSendWarning('Save or cancel the open draft first.');
    getMount()?.querySelector('.dr-comment-form')?.scrollIntoView({ block: 'center', behavior: 'smooth' });
    return;
  }
  if (diffState.comments.size === 0) return;
  const sessionId = diffState.ctx?.sessionId;
  if (!sessionId) { setDiffSendWarning('No active session.'); return; }
  const text = formatDiffReviewMessage();

  const step = liveOrchestratedStep();
  if (step) {
    try {
      await work.messageStep(diffState.ctx.jobId, step.id, text);
    } catch (e) {
      setDiffSendWarning(`Not sent: ${e?.message ?? e}`);
      return;
    }
    diffState.comments.clear();
    closeDiffOverlay();
    return;
  }

  try {
    await fetch(`/api/sessions/${encodeURIComponent(sessionId)}/git/review`, {
      method: 'POST',
      headers: { 'content-type': 'application/json' },
      body: JSON.stringify({ text }),
    });
  } catch { /* network hiccup — fall through to chat path */ }
  if (!tabSendUserMessage(sessionId, text)) {
    setDiffSendWarning('Disconnected — not sent. Try again once reconnected.');
    return;
  }
  sessions.for(sessionId).appendTranscript({ role: 'user', text });
  _deps.startThinking(sessionId);
  diffState.comments.clear();
  closeDiffOverlay();
  _deps.renderSession();
  _deps.scrollTranscriptBottom();
}

// ── Header sync: branch chip, PR link, ahead/behind, pull/push ────────────
function maybeRefreshHeaderBranch(sessionId) {
  if (!sessionId) return;
  const cached = getGitHeader(sessionId);
  if (cached?.branch != null || cached?.inFlight) return;
  setGitHeader(sessionId, { inFlight: true });
  fetch(`/api/sessions/${encodeURIComponent(sessionId)}/git/status`)
    .then((r) => r.ok ? r.json() : null)
    .then((data) => {
      if (!data) return;
      setGitHeader(sessionId, { branch: data.branch ?? null, prUrl: data.prUrl ?? null });
      const sv = sessions.get();
      if (sv.currentSessionId === sessionId && sv.view === 'session') _deps.renderSession();
    })
    .catch(() => {})
    .finally(() => { setGitHeader(sessionId, { inFlight: false }); });
}

async function refreshSourceControl(sessionId) {
  const id = sessionId ?? diffState.ctx?.sessionId;
  if (!id) return;
  let status = null; let log = [];
  try {
    const [sResp, lResp] = await Promise.all([
      fetch(`/api/sessions/${encodeURIComponent(id)}/git/status`),
      fetch(`/api/sessions/${encodeURIComponent(id)}/git/log?limit=30`),
    ]);
    status = sResp.ok ? await sResp.json() : null;
    log = lResp.ok ? ((await lResp.json()).entries ?? []) : [];
  } catch { status = null; }
  if (diffState.ctx?.sessionId !== id) return; // overlay moved on while we were fetching
  sourceCtl.status = status;
  sourceCtl.log = log;
  if (sourceCtl.status) {
    setGitHeader(id, { branch: sourceCtl.status.branch ?? null, prUrl: sourceCtl.status.prUrl ?? null });
    // Every commit/discard/stage in here ends up back at this refresh, and none of them mutate
    // the step — so this is the only thing that can take the tracked timeline's diff button
    // back out of its accent variant once the user has actually dealt with the changes.
    worktreeChanges.note(id, sourceCtl.status);
  }
  renderHeaderStats();
  renderFooter();
  if (diffState.mode === 'log') renderSourceLog();
  applyStagedStateToCards();
  const sv = sessions.get();
  if (sv.currentSessionId === id && sv.view === 'session') _deps.renderSession();
}

function renderSourceLog() {
  const listEl = getMount()?.querySelector('#dr-log');
  if (!listEl) return;
  if (!sourceCtl.log || sourceCtl.log.length === 0) {
    listEl.innerHTML = '<div class="dr-empty">No commits yet.</div>';
    return;
  }
  const base = sourceCtl.status?.commitUrlBase;
  listEl.innerHTML = sourceCtl.log.map((c) => {
    const when = sourceFormatRelative(c.date);
    const inner = `
      <span class="dr-log-hash">${escapeHtml(c.shortHash)}</span>
      <span class="dr-log-subject">${escapeHtml(c.subject)}</span>
      <span class="dr-log-meta">${escapeHtml(c.author)} · ${escapeHtml(when)}</span>`;
    return base
      ? `<a class="dr-log-row" href="${escapeHtml(base)}/commit/${escapeHtml(c.hash)}" target="_blank" rel="noopener noreferrer">${inner}</a>`
      : `<div class="dr-log-row">${inner}</div>`;
  }).join('');
}

function sourceFormatRelative(ms) {
  if (!Number.isFinite(ms) || ms <= 0) return '';
  const diff = Date.now() - ms;
  if (diff < 60_000) return 'just now';
  const m = Math.floor(diff / 60_000);
  if (m < 60) return `${m}m ago`;
  const h = Math.floor(m / 60);
  if (h < 24) return `${h}h ago`;
  const d = Math.floor(h / 24);
  if (d < 30) return `${d}d ago`;
  const months = Math.floor(d / 30);
  if (months < 12) return `${months}mo ago`;
  return `${Math.floor(months / 12)}y ago`;
}

function setSourceFeedback(kind, title, detail) {
  // While the mobile commit sheet is open it covers the overlay's #dr-feedback
  // banner, so route feedback into the sheet's own slot instead.
  const el = commitSheetEl?.querySelector('#dr-sheet-feedback') ?? getMount()?.querySelector('#dr-feedback');
  if (!el) return;
  if (!title) { el.hidden = true; el.textContent = ''; el.removeAttribute('data-kind'); return; }
  el.hidden = false;
  el.setAttribute('data-kind', kind);
  el.textContent = '';
  const head = document.createElement('div');
  head.textContent = title;
  el.appendChild(head);
  if (detail) { const pre = document.createElement('pre'); pre.textContent = detail; el.appendChild(pre); }
  const dismiss = document.createElement('button');
  dismiss.type = 'button'; dismiss.className = 'dr-feedback-dismiss'; dismiss.textContent = 'Dismiss';
  dismiss.onclick = () => setSourceFeedback();
  el.appendChild(dismiss);
}

// ── Footer: commit dialog + push/pull + primary CTA ──────────────────────
// `ignoreReview` is mobile-only: desktop folds the whole footer into a single
// "Submit review" CTA whenever there are drafted comments (reviewMode below);
// mobile instead surfaces Request-changes as its own sticky-bar button (P3
// brief's "three termination buttons") and keeps this label on its normal
// commit/push meaning so the two don't collide.
function computePrimaryLabel({ ignoreReview = false } = {}) {
  if (!ignoreReview && activeCommentCount() > 0) return `Submit review · ${activeCommentCount()}`;
  const s = sourceCtl.status;
  const commit = diffState.commit;
  if (!s) return 'Commit & push';
  const isWorktree = Boolean(s.worktree);
  const willCommit = !s.clean;
  if (!isWorktree) {
    const onDefault = Boolean(s.branch && s.defaultBranch && s.branch === s.defaultBranch);
    const bits = [];
    bits.push(willCommit ? 'Commit' : null);
    bits.push(commit.push ? 'push' : null);
    bits.push(commit.openPr && !s.prUrl && !onDefault ? (commit.draftPr ? 'open draft PR' : 'open PR') : null);
    const parts = bits.filter(Boolean);
    return parts.length ? parts[0] + (parts.length > 1 ? ` & ${parts.slice(1).join(' & ')}` : '') : 'Push';
  }
  if (commit.mergeMode === 'merge-to-base') return 'Squash & merge';
  if (!commit.openPr || s.prUrl) return 'Commit & push';
  return commit.draftPr ? 'Squash, push & open draft PR' : 'Squash, push & open PR';
}

// The commit dialog markup (message + merge mode + branch target + push/PR
// checkboxes) — shared by desktop's inline footer and mobile's commit sheet, so
// both hosts render the identical controls (D2). Reads the live commit draft +
// git status; produces no listeners (see wireCommitDialogEvents).
function buildCommitDialogHtml() {
  // Starts (or restores from cache) the PR draft the moment the dialog shows PR fields.
  ensurePrDraft();
  const s = sourceCtl.status;
  const busy = getGitBusy(diffState.ctx?.sessionId);
  const commit = diffState.commit;
  const isWorktree = Boolean(s?.worktree);
  // Non-worktree (primary checkout): the branch is an editable input, not a
  // static pill — typing a new name and pressing Enter moves the work onto a
  // fresh branch (git checkout -b), the escape hatch from committing straight
  // onto the default branch.
  const branchChip = isWorktree
    ? (commit.mergeMode === 'squash-to-branch'
      ? `<input class="dr-branch-input" id="dr-new-branch" value="${escapeHtml(commit.newBranch)}" placeholder="fix/new-branch" spellcheck="false" autocomplete="off">`
      : `<span class="o-pill code">${escapeHtml(s?.worktree?.baseBranch ?? s?.defaultBranch ?? 'main')}</span>`)
    : `<input class="dr-branch-input" id="dr-switch-branch" value="${escapeHtml(s?.branch ?? '')}" placeholder="branch-name"
        spellcheck="false" autocomplete="off" ${busy ? 'disabled' : ''}
        title="Type a new name and press Enter to move your work onto a new branch">`;
  const mergeToggle = isWorktree ? `
    <div class="dr-segmented" role="tablist" aria-label="Merge mode">
      <button type="button" data-merge="squash-to-branch" class="${commit.mergeMode === 'squash-to-branch' ? 'is-active' : ''}">Squash to branch</button>
      <button type="button" data-merge="merge-to-base" class="${commit.mergeMode === 'merge-to-base' ? 'is-active' : ''}">Merge to base</button>
    </div>` : '';
  // On the default branch there's nothing to PR (main → main is a no-op), so
  // hide the checkbox until the user switches to a feature branch above.
  const onDefaultBranch = Boolean(s?.branch && s?.defaultBranch && s.branch === s.defaultBranch);
  // Once a PR is already open for this branch, "open PR" is a no-op that would
  // 409 on `gh pr create` — so drop the checkbox entirely and link the existing
  // PR instead. A disabled-but-still-checked box reads as "this will open a
  // second PR" and paralyzes the user right when they need to just commit & push.
  const openPrRow = (!isWorktree || commit.mergeMode === 'squash-to-branch')
    && !(!isWorktree && onDefaultBranch)
    ? (s?.prUrl
      ? `<a class="dr-pr-open o-pill code" href="${escapeHtml(s.prUrl)}" target="_blank" rel="noopener">PR already open ↗</a>`
      : `<label class="dr-checkbox"><input type="checkbox" id="dr-openpr" ${commit.openPr ? 'checked' : ''}>Open PR to main</label>`
        + (commit.openPr ? `<label class="dr-checkbox" title="Let CI run before requesting reviewers"><input type="checkbox" id="dr-draftpr" ${commit.draftPr ? 'checked' : ''}>As draft</label>` : ''))
    : '';
  const prDraft = needsPrDraft();
  const prBlock = prDraft ? `
    <div class="dr-pr-draft">
      <div class="dr-commit-label o-microhead">
        Pull request
        <span class="dr-auto dr-pr-status" title="${escapeHtml(commit.prError)}">${escapeHtml(prDraftStatus(commit))}</span>
        <button type="button" class="dr-pr-redraft" ${commit.prDraft === 'drafting' ? 'disabled' : ''}>Redraft</button>
      </div>
      <input class="dr-pr-title" id="dr-pr-title" maxlength="200" placeholder="PR title" spellcheck="false" autocomplete="off" value="${escapeHtml(commit.prTitle)}">
      <textarea class="dr-commit-textarea dr-pr-body" id="dr-pr-body" maxlength="20000" placeholder="PR description">${escapeHtml(commit.prBody)}</textarea>
    </div>` : '';
  return `
    <div class="dr-commit-msg">
      <div class="dr-commit-label o-microhead">
        ${prDraft ? 'Commit message · this round' : 'Commit message'}
        ${commit.autoFilled ? '<span class="dr-auto">◐ drafted</span>' : ''}
        <span class="dr-commit-hint">⌘E edit · ⌘R regenerate</span>
      </div>
      <textarea class="dr-commit-textarea" id="dr-commit-textarea" maxlength="5000"
        placeholder="Describe the change…">${escapeHtml(commit.message)}</textarea>
    </div>
    ${prBlock}
    <div class="dr-commit-actions">
      ${mergeToggle}
      <div class="dr-commit-target">→ ${branchChip}</div>
      <label class="dr-checkbox"><input type="checkbox" id="dr-push" ${commit.push ? 'checked' : ''}>Push after commit</label>
      ${openPrRow}
    </div>`;
}

// Wire the commit-dialog inputs within `root` (the footer on desktop, the sheet
// on mobile). `onCommit.rerender` repaints the host in place when a toggle
// changes state — renderFooter for desktop, renderCommitSheet for the sheet.
function wireCommitDialogEvents(root, { onCommit }) {
  const ta = root.querySelector('#dr-commit-textarea');
  ta?.addEventListener('input', (e) => {
    diffState.commit.message = e.target.value;
    diffState.commit.autoFilled = false;
    root.querySelector('.dr-commit-label .dr-auto')?.remove();
    const primary = root.querySelector('.dr-primary');
    if (primary) primary.textContent = computePrimaryLabel({ ignoreReview: !isDesktop() });
  });
  root.querySelector('#dr-push')?.addEventListener('change', (e) => { diffState.commit.push = e.target.checked; onCommit.rerender(); });
  root.querySelector('#dr-openpr')?.addEventListener('change', (e) => { diffState.commit.openPr = e.target.checked; onCommit.rerender(); });
  root.querySelector('#dr-draftpr')?.addEventListener('change', (e) => { diffState.commit.draftPr = e.target.checked; onCommit.rerender(); });
  root.querySelector('#dr-new-branch')?.addEventListener('input', (e) => { diffState.commit.newBranch = e.target.value; });
  root.querySelector('#dr-pr-title')?.addEventListener('input', (e) => { diffState.commit.prTitle = e.target.value; });
  root.querySelector('#dr-pr-body')?.addEventListener('input', (e) => { diffState.commit.prBody = e.target.value; });
  root.querySelector('.dr-pr-redraft')?.addEventListener('click', () => {
    const sessionId = diffState.ctx?.sessionId;
    if (!sessionId) return;
    diffState.commit.prTitle = '';
    diffState.commit.prBody = '';
    void draftPr(sessionId);
  });
  // Non-worktree branch switch: fires on Enter/blur (change), not per-keystroke,
  // so create-branch runs once with the final name. A no-op name just repaints
  // (restoring the current branch); runSourceAction re-fetches status + re-renders,
  // which reveals the now-relevant "Open PR to main" checkbox.
  root.querySelector('#dr-switch-branch')?.addEventListener('change', (e) => {
    const name = e.target.value.trim();
    const current = sourceCtl.status?.branch ?? '';
    if (!name || name === current) { onCommit.rerender(); return; }
    void runSourceAction('create-branch', 'git/create-branch',
      { body: JSON.stringify({ newBranch: name }) },
      { success: `Now on branch ${name}.`, failure: 'Branch switch failed.' });
  });
  for (const btn of root.querySelectorAll('[data-merge]')) {
    btn.addEventListener('click', () => { diffState.commit.mergeMode = btn.dataset.merge; onCommit.rerender(); });
  }
}

function renderFooter() {
  const foot = getMount()?.querySelector('#dr-foot');
  if (!foot) return;
  const s = sourceCtl.status;
  const busy = getGitBusy(diffState.ctx?.sessionId);
  const commit = diffState.commit;
  const mobile = !isDesktop();
  const reviewMode = !mobile && activeCommentCount() > 0;
  const isWorktree = Boolean(s?.worktree);

  const pullBtn = `<button class="dr-glyph-btn" id="dr-pull-btn" type="button" ${s?.detached || busy ? 'disabled' : ''}
      title="Pull from upstream" aria-label="Pull from upstream">↓<span class="dr-sync-count">${s?.behind > 0 ? s.behind : ''}</span></button>`;
  const pushBtn = `<button class="dr-glyph-btn" id="dr-push-btn" type="button" ${s?.detached || busy ? 'disabled' : ''}
      title="Push to upstream" aria-label="Push to upstream">↑<span class="dr-sync-count">${s?.ahead > 0 ? s.ahead : (s?.upstream ? '' : '+')}</span></button>`;

  // Mobile: the footer is just a slim bar (status + sync glyphs + one primary).
  // Commit controls live in a slide-up sheet (openCommitSheet) so the diff owns
  // the screen. The primary folds like desktop's: Request-changes while comments
  // are drafted, otherwise Commit… (opens the sheet).
  if (mobile) {
    const commentCount = activeCommentCount();
    const label = commentCount > 0 ? `Request changes · ${commentCount}` : 'Commit…';
    foot.innerHTML = `
      <div class="dr-foot-bar">
        <span class="dr-foot-status">${footStatusText(s)}</span>
        <div class="dr-foot-glyphs">${pullBtn}${pushBtn}</div>
        <button class="o-btn o-btn--primary dr-primary" id="dr-primary-btn" type="button" ${busy ? 'disabled' : ''}>
          ${busy ? 'Working…' : label}
        </button>
      </div>`;
    wireFooterEvents(foot, true);
    return;
  }

  const label = computePrimaryLabel({ ignoreReview: mobile });

  const baseLabel = s?.worktree?.baseBranch ?? s?.defaultBranch ?? 'main';
  const squashBtn = isWorktree ? `<button class="o-btn o-btn--default dr-btn" id="dr-squash-base-btn" type="button" ${busy ? 'disabled' : ''}
      title="Squash this branch's commits onto ${baseLabel} locally and complete the step">Squash to ${baseLabel}</button>` : '';

  let dialogHtml = '';
  if (reviewMode) {
    dialogHtml = `<div class="dr-foot-status">${activeCommentCount()} drafted comment${activeCommentCount() === 1 ? '' : 's'} — sends back to the session, worktree preserved.</div>`;
  } else if (diffState.ctx) {
    dialogHtml = buildCommitDialogHtml();
  } else {
    dialogHtml = `<div class="dr-foot-status" id="dr-footer-status">—</div>`;
  }

  foot.innerHTML = `
    <div class="dr-foot-bar">
      <span class="dr-foot-status">${footStatusText(s)}</span>
      <div class="dr-foot-glyphs">${pullBtn}${pushBtn}</div>
      ${squashBtn}
      <button class="o-btn o-btn--primary dr-primary" id="dr-primary-btn" type="button" ${busy ? 'disabled' : ''}>
        ${busy ? 'Working…' : label}
      </button>
    </div>
    <div class="dr-commit-dialog">${dialogHtml}</div>`;

  wireFooterEvents(foot, mobile);
}

function footStatusText(s) {
  if (!s) return '—';
  const parts = [];
  if (s.clean) parts.push('working tree clean');
  else {
    const tracked = s.files.filter((f) => f.index !== '?' && f.index !== '!');
    const staged = tracked.filter((f) => f.index !== '.' && f.index !== ' ').length;
    parts.push(staged > 0 ? `${staged} of ${tracked.length} staged` : `${tracked.length} file${tracked.length === 1 ? '' : 's'} changed`);
  }
  if (s.ahead > 0) parts.push(`↑${s.ahead} ahead`);
  if (s.behind > 0) parts.push(`↓${s.behind} behind`);
  return parts.join(' · ');
}

function wireFooterEvents(foot, mobile) {
  foot.querySelector('#dr-pull-btn')?.addEventListener('click', () => runSourceAction('pull', 'git/pull', {}, { success: 'Pull complete.', failure: 'Pull failed (fast-forward only).' }));
  foot.querySelector('#dr-push-btn')?.addEventListener('click', () => runSourceAction('push', 'git/push', {}, { success: 'Push complete.', failure: 'Push failed.' }));
  // Mobile's primary opens the commit sheet, except while inline comments are
  // drafted — then it submits the review, matching desktop's single-button fold
  // (which redirects the primary to submitReview() when comments exist).
  foot.querySelector('#dr-primary-btn')?.addEventListener('click',
    mobile
      ? () => { if (activeCommentCount() > 0) void submitReview(); else openCommitSheet(); }
      : runPrimaryAction);
  foot.querySelector('#dr-squash-base-btn')?.addEventListener('click', () => { void doSquashToBase(diffState.ctx?.sessionId); });
  if (!mobile) wireCommitDialogEvents(foot, { onCommit: { rerender: renderFooter } });
}

// ── Mobile commit sheet ───────────────────────────────────────────────────
// The commit/finalize controls live in a slide-up sheet on mobile so the diff
// owns the screen. Reuses the shared .sheet chrome + sheet-utils helpers, but
// with a raised stacking context (it opens over the diff scrim, z-index 1200)
// and a height cap in CSS instead of pinSheetBelowHeader (no #header here).
let commitSheetEl = null;
let commitSheetBackdrop = null;

function openCommitSheet() {
  if (commitSheetEl) return;
  const mount = getMount();
  if (!mount) return;
  setSourceFeedback(); // clear any stale overlay banner before it moves into the sheet
  const backdrop = document.createElement('div');
  backdrop.className = 'sheet-backdrop dr-commit-sheet-backdrop';
  const sheet = document.createElement('aside');
  sheet.className = 'sheet dr-commit-sheet';
  sheet.setAttribute('role', 'dialog');
  sheet.setAttribute('aria-modal', 'true');
  sheet.setAttribute('aria-label', 'Commit changes');
  mount.appendChild(backdrop);
  mount.appendChild(sheet);
  commitSheetEl = sheet;
  commitSheetBackdrop = backdrop;
  document.body.classList.add('dr-commit-sheet-open');
  renderCommitSheet();
  requestAnimationFrame(() => { backdrop.classList.add('open'); sheet.classList.add('open'); });
  noteSheetOpen(closeCommitSheet);
  backdrop.addEventListener('click', closeCommitSheet);
}

function closeCommitSheet() {
  if (!commitSheetEl) return;
  const sheet = commitSheetEl;
  const backdrop = commitSheetBackdrop;
  commitSheetEl = null;
  commitSheetBackdrop = null;
  document.body.classList.remove('dr-commit-sheet-open');
  sheet.classList.remove('open');
  backdrop?.classList.remove('open');
  noteSheetClose();
  setTimeout(() => { sheet.remove(); backdrop?.remove(); }, 380);
}

function renderCommitSheet() {
  const sheet = commitSheetEl;
  if (!sheet) return;
  const s = sourceCtl.status;
  const busy = getGitBusy(diffState.ctx?.sessionId);
  const isWorktree = Boolean(s?.worktree);
  const baseLabel = s?.worktree?.baseBranch ?? s?.defaultBranch ?? 'main';
  const squashBtn = isWorktree
    ? `<button class="o-btn o-btn--default dr-btn" id="dr-squash-base-btn" type="button" ${busy ? 'disabled' : ''}
        title="Squash this branch's commits onto ${baseLabel} locally and complete the step">Squash to ${baseLabel}</button>`
    : '';
  const label = computePrimaryLabel({ ignoreReview: true });
  sheet.innerHTML = `
    <div class="grabber"></div>
    <div class="header-row">
      <span class="sheet-title">Commit changes</span>
      <button class="sheet-close" type="button" id="dr-sheet-close" aria-label="Close">✕</button>
    </div>
    <div class="dr-feedback dr-sheet-feedback" id="dr-sheet-feedback" hidden></div>
    <div class="dr-commit-dialog">${buildCommitDialogHtml()}</div>
    <div class="dr-sheet-actions">
      <button class="o-btn o-btn--danger dr-btn" id="dr-sheet-discard" type="button">Discard all</button>
      ${squashBtn}
      <button class="o-btn o-btn--primary dr-primary" id="dr-sheet-commit-btn" type="button" ${busy ? 'disabled' : ''}>
        ${busy ? 'Working…' : label}
      </button>
    </div>`;
  wireCommitDialogEvents(sheet, { onCommit: { rerender: renderCommitSheet } });
  sheet.querySelector('#dr-sheet-close')?.addEventListener('click', closeCommitSheet);
  sheet.querySelector('#dr-sheet-commit-btn')?.addEventListener('click', () => { void runCommitAction(); });
  sheet.querySelector('#dr-squash-base-btn')?.addEventListener('click', () => { void doSquashToBase(diffState.ctx?.sessionId); });
  sheet.querySelector('#dr-sheet-discard')?.addEventListener('click', () => { void discardAll(); });
  // innerHTML rebuild replaces the grabber/header-row handles, so rebind the
  // drag-to-dismiss gesture each render (makeSheetDismissible is idempotent).
  makeSheetDismissible(sheet, closeCommitSheet);
}

async function runSourceAction(kind, path, fetchOpts, msgs) {
  const sessionId = diffState.ctx?.sessionId;
  if (!sessionId) return false;
  setGitBusy(sessionId, kind);
  setSourceFeedback();
  renderFooter();
  try {
    const r = await fetch(`/api/sessions/${encodeURIComponent(sessionId)}/${path}`, {
      method: 'POST',
      headers: { 'content-type': 'application/json' },
      ...fetchOpts,
    });
    const body = await r.json().catch(() => null);
    if (diffState.ctx?.sessionId !== sessionId) return false;
    if (r.ok && body?.ok) {
      const detail = [body.stdout, body.stderr].filter((s) => s && s.trim().length > 0).join('\n').trim();
      setSourceFeedback('ok', msgs.success, detail || null);
      if (body.status) {
        sourceCtl.status = body.status;
        setGitHeader(sessionId, { branch: body.status.branch ?? null, prUrl: body.status.prUrl ?? null });
      }
      if (['commit', 'pull', 'create-branch', 'open-pr', 'discard'].includes(kind)) {
        try {
          const l = await fetch(`/api/sessions/${encodeURIComponent(sessionId)}/git/log?limit=30`);
          if (l.ok) sourceCtl.log = (await l.json()).entries ?? [];
        } catch { /* leave log as-is */ }
        if (kind === 'commit' || kind === 'discard') diffState.collapsed.clear();
        if (diffState.mode !== 'log') fetchAndRenderDiff();
      }
      return true;
    }
    const detail = body
      ? [body.stderr, body.stdout].filter((s) => s && s.trim().length > 0).join('\n').trim() || body.error
      : `HTTP ${r.status}`;
    setSourceFeedback('err', msgs.failure, detail || null);
    if (body?.status) sourceCtl.status = body.status;
    return false;
  } catch (err) {
    if (diffState.ctx?.sessionId !== sessionId) return false;
    setSourceFeedback('err', msgs.failure, String(err.message ?? err));
    return false;
  } finally {
    setGitBusy(sessionId, null);
    if (diffState.ctx?.sessionId === sessionId) {
      renderFooter();
      if (commitSheetEl) renderCommitSheet();
      renderHeaderStats();
      if (diffState.mode === 'log') renderSourceLog();
      const sv = sessions.get();
      if (sv.currentSessionId && sv.view === 'session') _deps.renderSession();
    }
  }
}

async function doCommit(sessionId, message) {
  if (diffState.mode === 'worktree') {
    const stagedCount = sourceCtl.status?.files?.filter((f) => f.index !== '.' && f.index !== ' ' && f.index !== '?' && f.index !== '!').length ?? 0;
    if (stagedCount === 0) {
      // Nothing explicitly staged — stage every change, including untracked files
      // (but not gitignored ones), so "Commit & push" behaves like a normal
      // "commit everything" action, matching the mockup's single-button happy path
      // (per-file staging remains available for users who want a partial commit instead).
      const paths = (sourceCtl.status?.files ?? []).filter((f) => f.index !== '!').map((f) => f.path);
      if (paths.length > 0) {
        const ok = await new Promise((resolve) => {
          fetch(`/api/sessions/${encodeURIComponent(sessionId)}/git/stage`, {
            method: 'POST', headers: { 'content-type': 'application/json' },
            body: JSON.stringify({ paths, action: 'stage' }),
          }).then((r) => r.json()).then((b) => { if (b?.status) sourceCtl.status = b.status; resolve(Boolean(b?.ok)); }).catch(() => resolve(false));
        });
        if (!ok) { setSourceFeedback('err', 'Auto-stage failed.'); return false; }
      }
    }
  }
  return runSourceAction('commit', 'git/commit', { body: JSON.stringify({ message }) }, { success: 'Commit created.', failure: 'Commit failed.' });
}

function doPush(sessionId) {
  return runSourceAction('push', 'git/push', {}, { success: 'Push complete.', failure: 'Push failed.' });
}

function doOpenPr(sessionId, draft) {
  return runSourceAction('open-pr', 'git/open-pr', { body: JSON.stringify({ draft }) }, { success: draft ? 'Draft pull request opened.' : 'Pull request opened.', failure: 'Open PR failed.' });
}

function doCreateBranch(sessionId, newBranch) {
  return runSourceAction('create-branch', 'git/create-branch', { body: JSON.stringify({ newBranch }) }, { success: 'Branch created.', failure: 'Branch creation failed.' });
}

async function doFinalize(sessionId, payload) {
  setGitBusy(sessionId, 'finalize');
  renderFooter();
  try {
    const r = await fetch(`/api/sessions/${encodeURIComponent(sessionId)}/git/finalize`, {
      method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify(payload),
    });
    const body = await r.json().catch(() => null);
    if (!r.ok || !body?.ok) {
      const detail = body ? [body.stderr, body.stdout].filter((s) => s && s.trim().length > 0).join('\n').trim() || body.error : `HTTP ${r.status}`;
      setSourceFeedback('err', 'Finalize failed.', detail || null);
      return false;
    }
    if (body.url) window.open(body.url, '_blank', 'noopener');
    // A squash-to-branch append that fast-forwards an already-open PR returns no url —
    // don't claim "PR opened" in that case (only a fresh open / self-heal carries a url).
    const okMsg = payload.kind === 'merge-to-base' ? 'Merged.' : (body.url ? 'PR opened.' : 'Pushed to PR.');
    setSourceFeedback('ok', okMsg, body.url || null);
    if (body.warning) showStatusToast(`PR opened, but: ${body.warning}`);
    try { await fetch(`/api/sessions/${encodeURIComponent(sessionId)}/archive`, { method: 'POST' }); } catch { /* manual archive fallback */ }
    closeDiffOverlay();
    _deps.leaveSession();
    return true;
  } catch (err) {
    setSourceFeedback('err', 'Finalize failed.', String(err.message ?? err));
    return false;
  } finally {
    setGitBusy(sessionId, null);
  }
}

async function doSquashToBase(sessionId) {
  const ctx = diffState.ctx;
  const s = sourceCtl.status;
  if (!sessionId || !s || getGitBusy(sessionId)) return false;
  const message = diffState.commit.message.trim();
  // The squash-merge collapses the branch's commits onto base, so anything still
  // uncommitted in the worktree must be committed first (mirrors runCommitAction's
  // merge-to-base path). No commits + clean tree with nothing ahead → route 409s.
  // Dirty tree → need a message to commit first. Clean + non-step → the server needs
  // it as the squash commit message. Clean + step → server derives it from the job.
  const needsMessage = !s.clean || !ctx?.stepId;
  if (needsMessage && !message) { setSourceFeedback('err', 'Commit message required.'); return false; }
  if (!s.clean && !(await doCommit(sessionId, message))) return false;
  setGitBusy(sessionId, 'finalize');
  renderFooter();
  try {
    const r = await fetch(`/api/sessions/${encodeURIComponent(sessionId)}/git/squash-to-base`, {
      method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify({ message }),
    });
    const body = await r.json().catch(() => null);
    const status = body?.status;
    if (status === 'merged') {
      setSourceFeedback('ok', 'Squashed to base.');
      // Step sessions are closed+archived server-side when the step resolves; a plain
      // session has no step, so archive it here like doFinalize does.
      if (!ctx?.stepId) { try { await fetch(`/api/sessions/${encodeURIComponent(sessionId)}/archive`, { method: 'POST' }); } catch { /* fallback */ } }
      closeDiffOverlay();
      _deps.leaveSession();
      return true;
    }
    // A diverged base is the user's to resolve: the automatic resolve-round handoff is
    // gone, so name the conflicting files and leave the overlay open to retry.
    if (status === 'conflict') {
      setSourceFeedback('err', 'Base has diverged — resolve conflicts manually, then retry.', (body.files || []).join('\n') || null);
      return false;
    }
    setSourceFeedback('err', 'Squash to base failed.', body?.message || `HTTP ${r.status}`);
    return false;
  } catch (err) {
    setSourceFeedback('err', 'Squash to base failed.', String(err.message ?? err));
    return false;
  } finally {
    setGitBusy(sessionId, null);
  }
}

// Desktop's single-button dispatcher: folds into submitReview() while
// per-hunk comments are drafted, otherwise runs the commit/push/PR path.
async function runPrimaryAction() {
  if (activeCommentCount() > 0) { await submitReview(); return; }
  await runCommitAction();
}

// The commit/push/PR path proper — also mobile's #dr-primary-btn handler
// directly (bypassing the reviewMode fold above), since mobile surfaces
// Request-changes as its own sticky-bar button instead.
async function runCommitAction() {
  const ctx = diffState.ctx;
  const sessionId = ctx?.sessionId;
  if (!sessionId || getGitBusy(sessionId)) return;

  const s = sourceCtl.status;
  if (!s) return;
  const commit = diffState.commit;
  const message = commit.message.trim();
  const isWorktree = Boolean(s.worktree);

  if (!isWorktree) {
    if (!s.clean) {
      if (!message) { setSourceFeedback('err', 'Commit message required.'); return; }
      if (!(await doCommit(sessionId, message))) return;
    }
    if (commit.push && !(await doPush(sessionId))) return;
    const live = sourceCtl.status ?? s;
    const onDefault = Boolean(live.branch && live.defaultBranch && live.branch === live.defaultBranch);
    if (commit.openPr && !live.prUrl && !onDefault) await doOpenPr(sessionId, commit.draftPr);
    return;
  }

  if (!message) { setSourceFeedback('err', 'Commit message required.'); return; }
  // Decided before the round's own commit below, which turns "dirty" into one more commit.
  const pr = needsPrDraft() ? { prTitle: commit.prTitle.trim(), prBody: commit.prBody.trim() } : null;
  if (pr && !pr.prTitle) {
    setSourceFeedback('err', commit.prDraft === 'drafting' ? 'The PR description is still drafting.' : 'PR title required.');
    return;
  }
  if (!s.clean && !(await doCommit(sessionId, message))) return;

  if (commit.mergeMode === 'merge-to-base') {
    await doFinalize(sessionId, { kind: 'merge-to-base', message, push: commit.push });
    return;
  }
  if (commit.openPr && !s.prUrl) {
    const newBranch = commit.newBranch.trim();
    if (!newBranch) { setSourceFeedback('err', 'Branch name required.'); return; }
    await doFinalize(sessionId, { kind: 'squash-to-branch', message, newBranch, draft: commit.draftPr, ...(pr ?? {}) });
    return;
  }
  // "Open PR" unchecked on squash-to-branch: finalize's squash-to-branch endpoint
  // always opens a PR via `gh`, so an unchecked box can't route through it without
  // a backend change. Still honor the typed branch name rather than silently
  // discarding it: switch the worktree onto it (carrying the just-made commit)
  // before pushing, matching the mockup's "just pushing a WIP" note.
  const typedBranch = commit.newBranch.trim();
  if (typedBranch && typedBranch !== s.branch) {
    if (!(await doCreateBranch(sessionId, typedBranch))) return;
  }
  if (commit.push) await doPush(sessionId);
}

export function initDiffOverlay(deps) {
  _deps = { ..._deps, ...deps };
  installAppBridge({ openDiffForStep });
  // Installed once at boot (not per-mount) — onGlobalKeydown no-ops whenever the
  // overlay isn't open, so a single listener for the app's lifetime is correct
  // and avoids stacking a duplicate on every openDiffOverlay() call.
  document.addEventListener('keydown', onGlobalKeydown);
}

export {
  openDiffOverlay,
  openDiffForStep,
  closeDiffOverlay,
  resetGitViewer,
  maybeRefreshHeaderBranch,
  refreshSourceControl,
};
