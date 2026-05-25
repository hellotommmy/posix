# Agent Hunt Rule Search Notes

Date: 2026-05-22

Question: is the full Agent Hunt multi-agent rules file public?

## What Was Found

The 130k Lines Formal Topology paper includes a full example of the
single-agent `CLAUDE.md` rules file in its "Current Prompt" section. The local
source file is:

- `C:\Users\Chengsong\Documents\AIPV2026Notes\topology-130k-src\afgpt-arxiv3.tex`

Relevant source region:

- "Current Prompt"
- "Prompting Automation"
- "Context Compactification"

The Agent Hunt arXiv source was also inspected locally:

- `%TEMP%\agenthunt_2603\agenthunt-arxiv-nc.tex`

Relevant source regions:

- initial statement-blueprint phase: formalize definitions/theorems first,
  without proofs, and double-check them before multi-agent work;
- multi-agent setup summary: four agents, bounties, locks, frequent
  pull-commit-push cycles, local guards, and no statement changes;
- guard scripts: later stream-based checks tracked `Qed` versus `Admitted`,
  lock validity, balances, and definition/theorem statement immutability.

The repeated short prompt was:

```text
Read the file CLAUDE.md . Treat it as authoritative work instructions. Follow those instructions exactly for all subsequent actions and responses. That means work as long as possible (as specified) without stopping.
```

The Agent Hunt paper says its four-agent setup largely followed that
`CLAUDE.md` style and modified it for bounties, locks, and multiple agents. It
reports a 234-line modified rules summary, but the full multi-agent file was
not present in the local arXiv source.

## GitHub Checks Run

Commands run locally:

```powershell
gh search code 'CLAUDE.md repo:mgwiki/mgw_test' --limit 20
gh search code '"Rules for Working on Math_Background.mg"' --limit 20
gh search code 'CLAUDE.md repo:mgwiki/alg_top' --limit 20
gh api repos/mgwiki/mgw_test/git/trees/main?recursive=1 --jq '.tree[].path' | Select-String -Pattern 'CLAUDE|AGENTS|RULE|PROGRESS|DEPS|CHANGES|guard|bounty|lock'
gh api repos/mgwiki/alg_top/git/trees/main?recursive=1 --jq '.tree[].path' | Select-String -Pattern 'CLAUDE|AGENTS|RULE|PROGRESS|DEPS|CHANGES|guard|bounty|lock|NOTICE'
```

Result:

- no public `CLAUDE.md` or `AGENTS.md` found in `mgwiki/mgw_test`;
- no public `CLAUDE.md` or `AGENTS.md` found in `mgwiki/alg_top`;
- `mgwiki/alg_top` does include `bin/mgdeps6.pl` and `forum/NOTICEBOARD.md`;
- public theorem files include bounty/proven comments, but not the full agent
  rule file.

## Sources

- Agent Hunt paper: https://arxiv.org/abs/2603.06737
- 130k Lines Formal Topology paper: https://arxiv.org/abs/2601.03298
- Isabelle System Manual, `isabelle build`: https://isabelle.in.tum.de/dist/library/Doc/System/Sessions.html
- Isabelle2025-2 Docker image: https://hub.docker.com/r/makarius/isabelle/tags
- Isabelle2025-2 NEWS, `sorry` rejected by build: https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/Isabelle2025-2/doc/NEWS.html
- Public algebraic topology repository: https://github.com/mgwiki/alg_top
- Public general topology repository used in the paper: https://github.com/mgwiki/mgw_test

## Conclusion

The single-agent rules are public in the 130k paper. The exact multi-agent
Agent Hunt rules file appears not to be public in the checked repositories. The
local `CLAUDE.md` in this POSIX repository is therefore a plausible adaptation
based on the public single-agent rules and the Agent Hunt paper's stated
principles: frozen statement layer, bounties, locks, frequent git sync, local
guard/build checks, progress files, and careful merge stewardship.
