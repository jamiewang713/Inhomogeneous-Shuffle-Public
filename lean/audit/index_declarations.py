"""Index the implementation and refresh the complete public-declaration audit."""

import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
index = []
for path in sorted((root / "Shuffle").glob("*.lean")):
    stack = []
    declarations = []
    source = path.read_text()
    for line_number, line in enumerate(source.splitlines(), 1):
        namespace = re.match(r"^namespace ([\w.]+)\s*$", line)
        section = re.match(r"^(?:noncomputable )?section(?:\s+(\w+))?\s*$", line)
        end = re.match(r"^end(?:\s+([\w.]+))?\s*$", line)
        if namespace:
            stack.append(("namespace", namespace[1]))
        elif section:
            stack.append(("section", section[1]))
        elif end and stack:
            stack.pop()
        declaration = re.match(
            r"^(?:@\[[^\]]+\]\s*)?(theorem|def|structure|abbrev)\s+([\w.]+)", line
        )
        if declaration:
            prefix = ".".join(name for kind, name in stack if kind == "namespace")
            name = prefix + "." + declaration[2] if prefix else declaration[2]
            declarations.append({"kind": declaration[1], "name": name, "line": line_number})
    index.append({
        "module": "Shuffle." + path.stem,
        "path": "lean/" + str(path.relative_to(root)),
        "imports": re.findall(r"^import (\S+)", source, re.M),
        "declarations": declarations,
    })
(root / "audit/implementation_index.json").write_text(json.dumps(index, indent=2) + "\n")
names = [declaration["name"] for module in index for declaration in module["declarations"]
         if declaration["kind"] in ("theorem", "def")]
(root / "audit/PrintAxioms.lean").write_text(
    "import Shuffle\n\n" + "".join("#print axioms " + name + "\n" for name in names)
)
print(f"Indexed {len(index)} implementation modules; {len(names)} public definitions/theorems to audit.")
