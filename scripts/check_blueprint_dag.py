"""Check the dependency graph emitted by PlasTeX for each supplied directory."""

import json
from pathlib import Path
import subprocess
import sys

for directory in map(Path, sys.argv[1:]):
    html = (directory / "dep_graph_document.html").read_text()
    dot = html.split(".renderDot(`", 1)[1].split("`", 1)[0]
    graph = json.loads(subprocess.check_output(["dot", "-Tjson"], input=dot, text=True))
    names = {node["_gvid"]: node["name"] for node in graph["objects"]}
    edges = {node: [] for node in names}
    for arc in graph["edges"]:
        edges[arc["tail"]].append(arc["head"])
    visited, active = set(), set()

    def visit(node):
        if node in active:
            raise ValueError(f"{directory}: cycle through {names[node]}")
        if node in visited:
            return
        active.add(node)
        for neighbour in edges[node]:
            visit(neighbour)
        active.remove(node)
        visited.add(node)

    for node in names:
        visit(node)
    print(f"{directory}: {len(names)} nodes, {len(graph['edges'])} edges, no cycles")
