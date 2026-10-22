#!/usr/bin/env python3
"""Render the v4 foundations manuscript to PDF.

Pipeline (the one recorded in paper-v4-ship-checklist-2026-10-18.md):
python-markdown -> HTML -> WeasyPrint, DejaVu fonts, A4.
Written 2026-10-22 when §29 (the four-colors exhibit) was added at
Jeff's instruction, because the original in-environment render command
was not saved with the manuscript. Raw HTML in the source (the §29
color spans) passes through python-markdown untouched; WeasyPrint
honors the inline color styles.
"""
import markdown
from weasyprint import HTML

SRC = "acmd-machine-verified-foundations-v4-2026-10-18.md"
OUT = "acmd-machine-verified-foundations-v4-2026-10-18.pdf"

CSS = """
@page { size: A4; margin: 2.2cm 2cm; }
body { font-family: "DejaVu Serif", serif; font-size: 10.5pt;
       line-height: 1.45; text-align: justify; color: #111; }
h1 { font-family: "DejaVu Sans", sans-serif; font-size: 17pt;
     text-align: center; line-height: 1.25; }
h2 { font-family: "DejaVu Sans", sans-serif; font-size: 12.5pt;
     margin-top: 1.4em; text-align: left; }
h3 { font-family: "DejaVu Sans", sans-serif; font-size: 11pt; text-align: left; }
code { font-family: "DejaVu Sans Mono", monospace; font-size: 9pt; }
li { margin-bottom: 0.35em; }
"""

md_text = open(SRC, encoding="utf-8").read()
body = markdown.markdown(md_text, extensions=["extra"])
html = ("<!DOCTYPE html><html><head><meta charset='utf-8'>"
        f"<style>{CSS}</style></head><body>{body}</body></html>")
open("acmd-machine-verified-foundations-v4-2026-10-18.html", "w",
     encoding="utf-8").write(html)
HTML(string=html).write_pdf(OUT)
print("rendered", OUT)
