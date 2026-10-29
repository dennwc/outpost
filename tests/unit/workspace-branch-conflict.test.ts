import { describe, it, expect } from 'vitest';
import { mkdtempSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { workspaceError } from '../../src/work/workspace.js';

function repoWithBranches(...branches: string[]): string {
  const dir = mkdtempSync(join(tmpdir(), 'ws-conflict-'));
  execFileSync('git', ['init', '-q', '-b', 'main', dir]);
  execFileSync('git', ['-C', dir, '-c', 'user.email=t@e', '-c', 'user.name=T', 'commit', '--allow-empty', '-q', '-m', 'init']);
  for (const b of branches) execFileSync('git', ['-C', dir, 'branch', b]);
  return dir;
}

const writable = (repoCwd: string, branch: string) => ({ kind: 'writable' as const, repoCwd, branch });

describe('workspaceError — branch path conflicts', () => {
  it('refuses a branch nested under an existing branch', () => {
    const repo = repoWithBranches('refactor');
    expect(workspaceError(writable(repo, 'refactor/video-appsrc-bin'))).toMatch(/collides with existing ref "refs\/heads\/refactor"/);
  });

  it('refuses a branch that is a prefix of an existing branch', () => {
    const repo = repoWithBranches('refactor/a');
    expect(workspaceError(writable(repo, 'refactor'))).toMatch(/refs\/heads\/refactor\/a/);
  });

  it('refuses a branch nested under a remote-tracking ref', () => {
    const repo = repoWithBranches();
    execFileSync('git', ['-C', repo, 'update-ref', 'refs/remotes/origin/refactor', 'HEAD']);
    expect(workspaceError(writable(repo, 'refactor/x'))).toMatch(/refs\/remotes\/origin\/refactor/);
  });

  it('accepts the branch itself and its siblings', () => {
    const repo = repoWithBranches('refactor/a', 'refactor-old');
    expect(workspaceError(writable(repo, 'refactor/a'))).toBeNull();
    expect(workspaceError(writable(repo, 'refactor/b'))).toBeNull();
  });

  it('skips the check when repoCwd is not a git repo', () => {
    expect(workspaceError(writable(mkdtempSync(join(tmpdir(), 'ws-none-')), 'refactor/x'))).toBeNull();
  });
});
