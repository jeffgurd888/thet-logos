#!/usr/bin/env python3
"""Axiomatic dependency graph for the thet-logos corpus.

Emits a machine-readable JSON graph with two layers:

  1. declaration -> axioms: for every declaration in the axiom-fence
     registry (scripts/axiom-fence.txt), its `#print axioms` set,
     collected in a single `lake env lean` run.
  2. module -> modules: for EVERY .lean file under ThetLogos/, the
     direct `import` edges to other ThetLogos modules (external imports
     such as Mathlib.* are counted per module, not expanded), plus the
     size of each module's transitive ThetLogos closure.

Scope, honestly: layer 2 covers the whole tree (parsing is cheap).
Layer 1 covers exactly the registered declarations — the same named
subset the axiom fence enforces. Growing layer 1 = admitting more
declarations to the registry (one local fence run per admission).

Usage:  python3 scripts/axiom_graph.py [--out PATH] [--registry PATH]
Run from the lean/ directory. Default output: scripts/axiom-graph.json
"""
import argparse
import importlib.util
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

IMPORT_RE = re.compile(r"^import\s+(.+)$", re.M)
MODTOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")


def load_fence_parser():
    spec = importlib.util.spec_from_file_location(
        "run_axiom_fence", Path(__file__).with_name("run_axiom_fence.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.parse_registry


def module_graph(lean_root: Path):
    files = sorted((lean_root / "ThetLogos").rglob("*.lean"))
    modules = {}
    for f in files:
        rel = f.relative_to(lean_root).with_suffix("")
        name = ".".join(rel.parts)
        text = f.read_text(encoding="utf-8", errors="replace")
        internal, external = set(), set()
        for m in IMPORT_RE.finditer(text):
            for tok in MODTOKEN_RE.findall(m.group(1)):
                if tok.startswith("ThetLogos."):
                    if tok != name:
                        internal.add(tok)
                elif tok not in ("import",):
                    external.add(tok)
        modules[name] = {
            "imports": sorted(internal),
            "external_import_count": len(external),
        }
    # transitive closure sizes over internal edges
    def closure(start):
        seen, stack = set(), [start]
        while stack:
            cur = stack.pop()
            for nxt in modules.get(cur, {}).get("imports", []):
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
        return seen
    for name in modules:
        modules[name]["transitive_imports"] = len(closure(name))
    return modules


def declaration_axioms(lean_root: Path, registry: Path):
    parse_registry = load_fence_parser()
    imports, decls = parse_registry(registry)
    check_src = "\n".join(imports) + "\n\n" + "\n".join(
        f"#print axioms {d}" for d in decls) + "\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir="/tmp",
                                     delete=False) as fh:
        fh.write(check_src)
        check_path = fh.name
    proc = subprocess.run(["lake", "env", "lean", check_path],
                          cwd=str(lean_root), capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    owner = {}
    current = None
    for raw in registry.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line.startswith("import "):
            current = line.split(None, 1)[1]
        elif line and not line.startswith("#"):
            owner[line] = current
    result = {}
    for d in decls:
        m = re.search(re.escape(f"'{d}' depends on axioms: [") + r"([^\]]*)\]", out)
        if m:
            axioms = [a.strip() for a in m.group(1).split(",") if a.strip()]
        elif f"'{d}' does not depend on any axioms" in out:
            axioms = []
        else:
            axioms = None  # not reported — surfaced in the summary, not hidden
        result[d] = {"module": owner.get(d), "axioms": axioms}
    return result


def main() -> int:
    here = Path(__file__).resolve().parent.parent  # lean/
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(here / "scripts" / "axiom-graph.json"))
    ap.add_argument("--registry", default=str(here / "scripts" / "axiom-fence.txt"))
    args = ap.parse_args()

    modules = module_graph(here)
    decls = declaration_axioms(here, Path(args.registry))
    unreported = [d for d, v in decls.items() if v["axioms"] is None]

    graph = {
        "schema": "thet-logos/axiom-graph@1",
        "scope": {
            "module_layer": f"all {len(modules)} .lean files under lean/ThetLogos/ (direct import edges + transitive closure sizes)",
            "declaration_layer": "the axiom-fence registry only (scripts/axiom-fence.txt) — a named subset, not the whole corpus",
            "fence": ["propext", "Classical.choice", "Quot.sound"],
        },
        "declarations": decls,
        "modules": modules,
        "summary": {
            "module_nodes": len(modules),
            "module_edges": sum(len(v["imports"]) for v in modules.values()),
            "declarations_checked": len(decls),
            "declarations_unreported": unreported,
            "axiom_universe": sorted({a for v in decls.values()
                                      for a in (v["axioms"] or [])}),
        },
    }
    Path(args.out).write_text(json.dumps(graph, indent=1), encoding="utf-8")
    print(f"wrote {args.out}")
    print(f"modules: {graph['summary']['module_nodes']} nodes, "
          f"{graph['summary']['module_edges']} internal edges")
    print(f"declarations: {len(decls)} checked, unreported: {unreported}")
    print(f"axiom universe over checked declarations: {graph['summary']['axiom_universe']}")
    return 0 if not unreported else 1


if __name__ == "__main__":
    sys.exit(main())
