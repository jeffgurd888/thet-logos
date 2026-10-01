#!/usr/bin/env python3
"""Typeset the order-one-22 paper: arXiv-style PDF (reportlab) + .tex source."""
import re, os
from reportlab.lib.pagesizes import A4
from reportlab.lib.units import cm
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY, TA_LEFT
from reportlab.platypus import (BaseDocTemplate, PageTemplate, Frame, Paragraph,
                                Spacer, HRFlowable, KeepTogether, Table, TableStyle)
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont

SRC = os.path.expanduser("~/workspace/thet-logos/whitepaper/order-one-22-paper-draft.md")
OUTDIR = os.path.expanduser("~/workspace/your_files/thet-logos-paper")
os.makedirs(OUTDIR, exist_ok=True)
PDF = os.path.join(OUTDIR, "order-one-22-classification.pdf")
TEX = os.path.join(OUTDIR, "order-one-22-classification.tex")

FD = "/usr/share/fonts/truetype/dejavu/"
pdfmetrics.registerFont(TTFont("Serif", FD + "DejaVuSerif.ttf"))
pdfmetrics.registerFont(TTFont("Serif-Bold", FD + "DejaVuSerif-Bold.ttf"))
pdfmetrics.registerFont(TTFont("Mono", "/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf"))

# ---------------------------------------------------------------- parse ---
text = open(SRC).read().splitlines()
lines = [l for l in text if not l.startswith("%")]
blocks = []  # (kind, payload)
i, n = 0, len(lines)

def is_section_header(s):
    return re.match(r"^(\d+)\.\s+[A-Z]", s)

while i < n:
    l = lines[i]
    s = l.strip()
    if not s:
        i += 1; continue
    if s == "TITLE":
        i += 1; t = []
        while i < n and lines[i].strip(): t.append(lines[i].strip()); i += 1
        blocks.append(("title", " ".join(t))); continue
    if s == "AUTHOR":
        i += 1; a = []
        while i < n and lines[i].strip(): a.append(lines[i].strip()); i += 1
        blocks.append(("author", a)); continue
    if s == "ABSTRACT":
        i += 1; ps = []
        while i < n and not is_section_header(lines[i].strip()):
            if lines[i].strip(): ps.append(lines[i].strip())
            i += 1
        blocks.append(("abstract", [" ".join(ps)])); continue
    if s == "BIBLIOGRAPHY":
        i += 1; entries = []; cur = None
        while i < n and not lines[i].strip().startswith("APPENDIX"):
            m = re.match(r"^\[(\d+)\]\s*(.*)$", lines[i].strip())
            if m:
                if cur: entries.append(cur)
                cur = [m.group(1), m.group(2)]
            elif cur and lines[i].strip():
                cur[1] += " " + lines[i].strip()
            i += 1
        if cur: entries.append(cur)
        blocks.append(("bib", entries)); continue
    if s.startswith("APPENDIX"):
        m = re.match(r"^APPENDIX\s+([A-Z])\.\s*(.*)$", s)
        blocks.append(("appendix_head", m.group(2)))
        i += 1
        entries = []
        while i < n:
            if re.search(r"dirs22\s+\d+:", lines[i]):
                spans = [m for m in re.finditer(r"dirs22\s+(\d+):", lines[i])]
                for a, b in zip(spans, spans[1:] + [None]):
                    num = int(a.group(1))
                    rest = lines[i][a.end(): b.start() if b else len(lines[i])].strip()
                    entries.append((num, rest))
                i += 1
            elif lines[i].strip().startswith("SM directions") or lines[i].strip().startswith("Exotic directions"):
                blocks.append(("appendix_note", lines[i].strip())); i += 1
            elif lines[i].strip().startswith("Each exotic matrix"):
                para = [lines[i].strip()]; i += 1
                while i < n and lines[i].strip() and not lines[i].strip().startswith("dirs22"):
                    para.append(lines[i].strip()); i += 1
                blocks.append(("para", " ".join(para)))
            elif not lines[i].strip():
                i += 1
            else:
                para = [lines[i].strip()]; i += 1
                while i < n and lines[i].strip() and not re.match(r"^\s*dirs22\s+\d+:", lines[i]):
                    para.append(lines[i].strip()); i += 1
                blocks.append(("para", " ".join(para)))
        blocks.append(("appendix_entries", entries))
        continue
    m = re.match(r"^(\d+\.\d+)\.\s+(.*)$", s)
    if m:
        blocks.append(("subsection", (m.group(1), m.group(2)))); i += 1; continue
    m = re.match(r"^(\d+)\.\s+(.*)$", s)
    if m and s[0].isdigit() and m.group(2)[0].isupper():
        blocks.append(("section", (m.group(1), m.group(2)))); i += 1; continue
    if s == "ACKNOWLEDGMENTS":
        blocks.append(("section", ("", "ACKNOWLEDGMENTS"))); i += 1; continue
    if l.startswith("    "):
        d = []
        while i < n and lines[i].startswith("    "):
            d.append(lines[i].strip()); i += 1
        blocks.append(("display", d)); continue
    para = [s]; i += 1
    while i < n and lines[i].strip() and not lines[i].startswith("    ") \
            and not is_section_header(lines[i].strip()) \
            and not re.match(r"^(\d+\.\d+)\.\s+", lines[i].strip()) \
            and lines[i].strip() not in ("BIBLIOGRAPHY", "ACKNOWLEDGMENTS") \
            and not lines[i].strip().startswith("APPENDIX"):
        para.append(lines[i].strip()); i += 1
    blocks.append(("para", " ".join(para)))

# ------------------------------------------------------- unicode mapping ---
CODE_RE = re.compile(r"`([^`]+)`")

def U(t):
    codes = {}
    def stash(m):
        k = "\x00%d\x00" % len(codes)
        codes[k] = '<font face="Mono" size="9.5">%s</font>' % m.group(1)
        return k
    t = CODE_RE.sub(stash, t)
    reps = [
        ("M_{32}(C)", "M<sub>32</sub>(ℂ)"),
        ("M_32(C)", "M<sub>32</sub>(ℂ)"),
        ("M_3(C)", "M<sub>3</sub>(ℂ)"),
        ("C^32", "ℂ<sup>32</sup>"),
        ("(+)", "⊕"),
        ("C ⊕ H ⊕", "ℂ ⊕ ℍ ⊕"),
        ("(C)", "(ℂ)"), ("(H)", "(ℍ)"),
        ("A_F", "A<sub>F</sub>"),
        ("H_L^c", "H<sub>L</sub><super>c</super>"),
        ("H_R^c", "H<sub>R</sub><super>c</super>"),
        ("H_F", "H<sub>F</sub>"),
        ("H_L", "H<sub>L</sub>"), ("H_R", "H<sub>R</sub>"),
        ("D_F", "D<sub>F</sub>"),
        ("gamma_F", "γ<sub>F</sub>"),
        ("W_{22}", "W<sub>22</sub>"),
        ("W22", "W<sub>22</sub>"),
        ("b^o", "b°"),
        ("nu_L", "ν<sub>L</sub>"), ("nu_R", "ν<sub>R</sub>"),
        ("ebar_R", "ē<sub>R</sub>"),
        ("u_L", "u<sub>L</sub>"), ("d_R", "d<sub>R</sub>"),
        ("d_L", "d<sub>L</sub>"), ("u_R", "u<sub>R</sub>"),
        ("e_L", "e<sub>L</sub>"), ("e_R", "e<sub>R</sub>"),
        ("dim_R", "dim<sub>ℝ</sub>"), ("span_R", "span<sub>ℝ</sub>"),
        ("finrank R", "finrank ℝ"), ("Submodule.span R", "Submodule.span ℝ"),
        ("lambda_j", "λ<sub>j</sub>"), ("lambda_i", "λ<sub>i</sub>"),
        ("(lambda)", "(λ)"),
        ("mu_j", "μ<sub>j</sub>"), ("mu_i", "μ<sub>i</sub>"),
        ("(mu)", "(μ)"),
        ("M x F", "M × F"),
        ("32x32", "32×32"),
        ("D/Lambda", "D/Λ"),
        (":<->", " ↔ "),
        ("<->", "↔"),
        ("->", "→"),
        ("92 - 70 = 22", "92 − 70 = 22"),
        ("yNu", "y<sub>ν</sub>"), ("yE", "y<sub>E</sub>"),
        ("yU", "y<sub>U</sub>"), ("yD", "y<sub>D</sub>"), ("yR", "y<sub>R</sub>"),
        ("d/d Re(", "d/dRe("), ("d/d Im(", "d/dIm("),
        ("∎", "□"),
        ("--", "—"),
    ]
    for a, b in reps:
        t = t.replace(a, b)
    t = t.replace("\x00", "\x00")  # no-op keep
    for k, v in codes.items():
        t = t.replace(k, v)
    return t

RUNIN = re.compile(r"^(Hypothesis H \([^)]*\)\.|Theorem \([^)]*\)\.|Proof\.|Corollary\.|Explicit non-claims\.)")

def para_markup(t):
    t = U(t)
    m = RUNIN.match(t)
    if m:
        t = "<b>%s</b>%s" % (m.group(1), t[len(m.group(1)):])
    # citation markers [n] -> keep
    return t

# ----------------------------------------------------------------- styles ---
S_title = ParagraphStyle("title", fontName="Serif-Bold", fontSize=17, leading=21,
                         alignment=TA_CENTER, spaceAfter=10)
S_author = ParagraphStyle("author", fontName="Serif", fontSize=11, leading=14,
                          alignment=TA_CENTER, spaceAfter=2)
S_date = ParagraphStyle("date", fontName="Serif", fontSize=10, leading=13,
                        alignment=TA_CENTER, spaceAfter=14, textColor="#444444")
S_abstract = ParagraphStyle("abstract", fontName="Serif", fontSize=10, leading=14,
                           alignment=TA_JUSTIFY, leftIndent=1.2*cm, rightIndent=1.2*cm,
                           spaceBefore=6, spaceAfter=6)
S_sec = ParagraphStyle("sec", fontName="Serif-Bold", fontSize=13, leading=16,
                       spaceBefore=16, spaceAfter=8, keepWithNext=True)
S_sub = ParagraphStyle("sub", fontName="Serif-Bold", fontSize=11.5, leading=14.5,
                       spaceBefore=12, spaceAfter=6, keepWithNext=True)
S_body = ParagraphStyle("body", fontName="Serif", fontSize=10.5, leading=14.5,
                        alignment=TA_JUSTIFY, firstLineIndent=14, spaceAfter=4)
S_body0 = ParagraphStyle("body0", parent=S_body, firstLineIndent=0)
S_disp = ParagraphStyle("disp", fontName="Serif", fontSize=10.5, leading=14.5,
                        alignment=TA_LEFT, leftIndent=1.0*cm, spaceBefore=6, spaceAfter=6)
S_bib = ParagraphStyle("bib", fontName="Serif", fontSize=9.5, leading=13,
                       alignment=TA_LEFT, leftIndent=14, firstLineIndent=-14, spaceAfter=4)
S_app = ParagraphStyle("app", fontName="Serif", fontSize=10, leading=13.5,
                       alignment=TA_LEFT, leftIndent=0.8*cm, spaceAfter=2)
S_appnote = ParagraphStyle("appnote", parent=S_app, fontName="Serif-Bold", spaceBefore=8)

def footer(canvas, doc):
    canvas.saveState()
    canvas.setFont("Serif", 9)
    canvas.setFillColor("#666666")
    canvas.drawCentredString(A4[0]/2, 1.6*cm, str(doc.page))
    canvas.restoreState()

doc = BaseDocTemplate(PDF, pagesize=A4,
                      leftMargin=2.5*cm, rightMargin=2.5*cm,
                      topMargin=2.5*cm, bottomMargin=2.5*cm,
                      title="A 22-direction classification of the order-one commutant",
                      author="Jeffrey Michael Gurd")
frame = Frame(doc.leftMargin, doc.bottomMargin, doc.width, doc.height, id="f")
doc.addPageTemplates([PageTemplate(id="p", frames=[frame], onPage=footer)])

story = []
for kind, pay in blocks:
    if kind == "title":
        story.append(Paragraph(U(pay), S_title))
    elif kind == "author":
        for j, a in enumerate(pay):
            story.append(Paragraph(U(a), S_author))
        story.append(Paragraph("September 2026", S_date))
    elif kind == "abstract":
        story.append(Paragraph("<b>Abstract.</b> " + U(pay[0]), S_abstract))
        story.append(HRFlowable(width="100%", thickness=0.4, color="#999999",
                                spaceBefore=8, spaceAfter=8))
    elif kind == "section":
        num, head = pay
        story.append(Paragraph(U(("%s. %s" % (num, head)).strip(". ")), S_sec) if num
                     else Paragraph(U(head), S_sec))
    elif kind == "subsection":
        num, head = pay
        story.append(Paragraph(U(num + ". " + head), S_sub))
    elif kind == "para":
        story.append(Paragraph(para_markup(pay), S_body))
    elif kind == "display":
        for d in pay:
            story.append(Paragraph(U(d), S_disp))
    elif kind == "bib":
        story.append(Paragraph("BIBLIOGRAPHY", S_sec))
        for num, entry in pay:
            story.append(Paragraph("<b>[%s]</b> %s" % (num, U(entry)), S_bib))
    elif kind == "appendix_head":
        story.append(Paragraph("APPENDIX A. " + U(pay), S_sec))
    elif kind == "appendix_note":
        story.append(Paragraph(U(pay), S_appnote))
    elif kind == "appendix_entries":
        sm = sorted([(k, v) for k, v in pay if k < 10])
        ex = sorted([(k, v) for k, v in pay if k >= 10])
        for grp in (sm, ex):
            for k, v in grp:
                story.append(Paragraph(
                    "<font face=\"Mono\" size=\"9\">dirs22 %d</font>&nbsp;&nbsp;%s" % (k, U(v)),
                    S_app))
            story.append(Spacer(1, 6))

doc.build(story)
print("PDF written:", PDF, os.path.getsize(PDF), "bytes")
