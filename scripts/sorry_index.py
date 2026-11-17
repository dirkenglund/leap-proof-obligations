#!/usr/bin/env python3
"""Regenerate or check sorry-index.json.

The index records, for every obligation file in LeapProofObligations/
(other than Definitions.lean), the theorem name and the position of its
single `sorry`. Its `commit` field is the most recent commit that changed
the Lean sources (LeapProofObligations/ or LeapProofObligations.lean).
Every position in the index is valid at that commit and at every later
commit that leaves the Lean sources unchanged.

  python3 scripts/sorry_index.py write   # after committing Lean changes
  python3 scripts/sorry_index.py check   # used by CI
"""
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
INDEX = ROOT / "sorry-index.json"
SRC = "LeapProofObligations"
SOURCES = [SRC, "LeapProofObligations.lean"]
REMOTE = "https://github.com/dirkenglund/leap-proof-obligations"
NAMESPACE = "Leap"


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, check=True,
                          capture_output=True, text=True).stdout.strip()


def lean_version():
    return (ROOT / "lean-toolchain").read_text().strip().split(":")[-1]


def source_commit():
    return git("log", "-1", "--format=%H", "--", *SOURCES)


def entry(path, commit):
    text = (ROOT / path).read_text()
    names = re.findall(r"^theorem\s+([^\s(:{\[]+)", text, flags=re.M)
    hits = [(i + 1, m.start()) for i, line in enumerate(text.split("\n"))
            for m in re.finditer(r"\bsorry\b", line)
            if not line.lstrip().startswith("--")]
    if len(names) != 1 or len(hits) != 1:
        sys.exit(f"{path}: expected one theorem and one sorry, "
                 f"found {len(names)} and {len(hits)}")
    line, col = hits[0]
    return {
        "theorem": f"{NAMESPACE}.{names[0]}",
        "repo": {"remote": REMOTE, "branch": "main", "commit": commit,
                 "lean_version": lean_version()},
        "location": {"path": path, "start_line": line, "start_column": col + 1,
                     "end_line": line, "end_column": col + 6},
        "debug_info": {"goal": None,
                       "url": f"{REMOTE}/blob/{commit}/{path}#L{line}"},
    }


def build(commit, order):
    files = sorted(str(p.relative_to(ROOT)) for p in (ROOT / SRC).glob("*.lean")
                   if p.name != "Definitions.lean")
    rank = {p: i for i, p in enumerate(order)}
    files.sort(key=lambda p: (rank.get(p, len(rank)), p))
    return [entry(p, commit) for p in files]


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "check"
    data = json.loads(INDEX.read_text())
    order = [s["location"]["path"] for s in data["sorries"]]
    if mode == "write":
        if git("status", "--porcelain", "--", *SOURCES):
            sys.exit("commit the Lean sources first")
        data["sorries"] = build(source_commit(), order)
        INDEX.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
        print(f"wrote {len(data['sorries'])} entries at {source_commit()}")
        return
    commits = {s["repo"]["commit"] for s in data["sorries"]}
    if len(commits) != 1:
        sys.exit(f"index has {len(commits)} distinct commits")
    commit = commits.pop()
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        sys.exit(f"commit field is not a full SHA: {commit!r}")
    try:
        git("merge-base", "--is-ancestor", commit, "HEAD")
    except subprocess.CalledProcessError:
        sys.exit(f"{commit} is not an ancestor of HEAD; run `write`")
    if git("diff", "--name-only", commit, "HEAD", "--", *SOURCES):
        sys.exit(f"Lean sources changed since {commit}; run `write`")
    if data["sorries"] != build(commit, order):
        sys.exit("sorry-index.json is out of date; run `write`")
    print(f"sorry-index.json OK: {len(data['sorries'])} entries at {commit}")


if __name__ == "__main__":
    main()
