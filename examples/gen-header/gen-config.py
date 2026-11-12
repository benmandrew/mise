#!/usr/bin/env python3
"""Write a C header from KEY=VALUE lines: gen-config.py INPUT OUTPUT."""
import sys

src, out = sys.argv[1], sys.argv[2]
lines = ["/* generated from %s */" % src, "#pragma once"]
with open(src) as f:
    for line in f:
        line = line.strip()
        if line and not line.startswith("#"):
            key, _, value = line.partition("=")
            lines.append("#define %s %s" % (key.strip(), value.strip()))
text = "\n".join(lines) + "\n"
# The rule has `restat`, so mise's command wrapper compares the outputs: when
# the header comes out the same, it puts the old file back with its old mtime.
with open(out, "w") as f:
    f.write(text)
