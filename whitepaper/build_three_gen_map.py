#!/usr/bin/env python3
"""Build The Three-Generation Map report PDF (US Letter) from three-generation-map.md."""
import re
from reportlab.lib.units import inch as IN
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.colors import HexColor
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY, TA_LEFT
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (BaseDocTemplate, PageTemplate, Frame, Paragraph,
                                Spacer, HRFlowable, Table, TableStyle)

PAGE_W, PAGE_H = 8.5 * IN, 11 * IN
MARGIN = 1.0 * IN

pdfmetrics.registerFont(TTFont("Serif", "/usr/share/fonts/truetype/dejavu/DejaVuSerif.ttf"))
pdfmetrics.registerFont(TTFont("Serif-Bold", "/usr/share/fonts/truetype/dejavu/DejaVuSerif-Bold.ttf"))
pdfmetrics.registerFont(TTFont("Serif-Italic", "/usr/share/fonts/truetype/dejavu/DejaVuSerif.ttf"))
pdfmetrics.registerFont(TTFont("Mono", "/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf"))

INK = HexColor("#1a1a1a")
FAINT = HexColor("#666666")
LIGHT = HexColor("#f0f0f0")

sTitle = ParagraphStyle("Title", fontName="Serif-Bold", fontSize=22, leading=28,
                        alignment=TA_CENTER, textColor=INK, spaceAfter=6)
sSubtitle = ParagraphStyle("Subtitle", fontName="Serif", fontSize=13, leading=17,
                           alignment=TA_CENTER, textColor=INK, spaceAfter=18)
sAuthor = ParagraphStyle("Author", fontName="Serif-Bold", fontSize=11, leading=14,
                         alignment=TA_CENTER, textColor=INK, spaceAfter=2)
sAffil = ParagraphStyle("Affil", fontName="Serif-Italic", fontSize=10, leading=13,
                        alignment=TA_CENTER, textColor=FAINT, spaceAfter=2)
sMeta2 = ParagraphStyle("Meta2", fontName="Serif", fontSize=10, leading=13,
                        alignment=TA_CENTER, textColor=FAINT, spaceAfter=4)
sStatus = ParagraphStyle("Status", fontName="Serif-Italic", fontSize=9, leading=12,
                         alignment=TA_CENTER, textColor=FAINT, spaceAfter=18)
sH2 = ParagraphStyle("H2", fontName="Serif-Bold", fontSize=13, leading=16,
                     textColor=INK, spaceBefore=16, spaceAfter=8, keepWithNext=True)
sBody = ParagraphStyle("Body", fontName="Serif", fontSize=10.5, leading=15.5,
                       alignment=TA_JUSTIFY, textColor=INK, spaceAfter=7)
sMath = ParagraphStyle("Math", fontName="Mono", fontSize=9.5, leading=13.5,
                       alignment=TA_CENTER, textColor=INK, spaceBefore=6, spaceAfter=8,
                       backColor=LIGHT, borderPadding=(4, 4, 4))
sCell = ParagraphStyle("Cell", fontName="Serif", fontSize=9, leading=12, textColor=INK)
sCellH = ParagraphStyle("CellH", fontName="Serif-Bold", fontSize=9, leading=12, textColor=INK)
sBullet = ParagraphStyle("Bullet", fontName="Serif", fontSize=10.5, leading=15,
                         textColor=INK, spaceAfter=4, leftIndent=18,
                         firstLineIndent=0, bulletIndent=8)


def md_inline(t):
    t = t.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    t = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", t)
    t = re.sub(r"\*(.+?)\*", r"<i>\1</i>", t)
    t = re.sub(r"`(.+?)`", r'<font face="Mono">\1</font>', t)
    return t


def md_table(lines):
    rows = []
    for ln in lines:
        cells = [c.strip() for c in ln.strip().strip("|").split("|")]
        rows.append(cells)
    # drop the separator row (all dashes)
    rows = [r for r in rows if not all(set(c) <= set("-: ") for c in r)]
    data = [[Paragraph(md_inline(c), sCellH if i == 0 else sCell) for c in r]
            for i, r in enumerate(rows)]
    t = Table(data, repeatRows=1)
    t.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, 0), LIGHT),
        ("LINEBELOW", (0, 0), (-1, 0), 0.75, INK),
        ("LINEBELOW", (0, 1), (-1, -1), 0.25, FAINT),
        ("VALIGN", (0, 0), (-1, -1), "TOP"),
        ("LEFTPADDING", (0, 0), (-1, -1), 6),
        ("RIGHTPADDING", (0, 0), (-1, -1), 6),
        ("TOPPADDING", (0, 0), (-1, -1), 4),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 4),
    ]))
    return t


def build():
    src = open("three-generation-map.md").read()
    fm, body = {}, src
    m = re.match(r"^---\n(.*?)\n---\n", src, re.S)
    if m:
        for line in m.group(1).splitlines():
            if ":" in line:
                k, v = line.split(":", 1)
                fm[k.strip()] = v.strip().strip('"')
        body = src[m.end():]

    story = []
    story.append(Spacer(1, 1.0 * IN))
    story.append(Paragraph(fm.get("title", "").split(":")[0], sTitle))
    story.append(Paragraph(": ".join(fm.get("title", "").split(":")[1:]).strip(), sSubtitle))
    story.append(Paragraph(fm.get("author", ""), sAuthor))
    story.append(Paragraph(fm.get("affiliation", ""), sAffil))
    story.append(Paragraph(fm.get("date", "") + " — " + fm.get("version", ""), sMeta2))
    story.append(Paragraph(fm.get("status", ""), sStatus))
    story.append(HRFlowable(width="30%", thickness=0.5, color=FAINT,
                            spaceAfter=12, hAlign="CENTER", vAlign="BOTTOM"))

    in_math, math_buf, para_buf, table_buf = False, [], [], []

    def flush_para():
        if para_buf:
            t = " ".join(para_buf).strip()
            para_buf.clear()
            if t:
                if t.startswith("- "):
                    story.append(Paragraph(md_inline(t[2:]), sBullet, bulletText="•"))
                else:
                    story.append(Paragraph(md_inline(t), sBody))

    def flush_table():
        if table_buf:
            story.append(Spacer(1, 6))
            story.append(md_table(table_buf))
            story.append(Spacer(1, 8))
            table_buf.clear()

    for line in body.splitlines():
        s = line.strip()
        if s.startswith("$$"):
            if not in_math:
                flush_para(); flush_table()
                in_math, math_buf = True, [s.strip("$").strip()]
            else:
                math_buf.append(s.strip("$").strip())
                story.append(Paragraph(" ".join(x for x in math_buf if x), sMath))
                in_math = False
            continue
        if in_math:
            math_buf.append(s)
            continue
        if s.startswith("|"):
            flush_para()
            table_buf.append(s)
            continue
        else:
            flush_table()
        if not s:
            flush_para()
            continue
        if s.startswith("# "):
            continue
        if s.startswith("## "):
            flush_para()
            story.append(Paragraph(md_inline(s[3:]), sH2))
            continue
        if s.startswith("---"):
            continue
        if s.startswith("*") and s.endswith("*") and len(s) < 200 and not s.startswith("**"):
            flush_para()
            story.append(Paragraph(md_inline(s), sStatus))
            continue
        para_buf.append(s)
    flush_para(); flush_table()

    doc = BaseDocTemplate("three-generation-map.pdf",
                          pagesize=(PAGE_W, PAGE_H),
                          leftMargin=MARGIN, rightMargin=MARGIN,
                          topMargin=MARGIN, bottomMargin=MARGIN,
                          title=fm.get("title", ""), author=fm.get("author", ""))

    def footer(canvas, doc):
        canvas.saveState()
        canvas.setFont("Serif-Italic", 8)
        canvas.setFillColor(FAINT)
        canvas.drawCentredString(PAGE_W / 2, 0.6 * IN,
                                 f"{fm.get('title','').split(':')[0]} — {fm.get('version','')} — {doc.page}")
        canvas.restoreState()

    frame = Frame(MARGIN, MARGIN, PAGE_W - 2 * MARGIN, PAGE_H - 2 * MARGIN, id="f")
    doc.addPageTemplates([PageTemplate(id="p", frames=[frame], onPage=footer)])
    doc.build(story)
    print("wrote three-generation-map.pdf")


if __name__ == "__main__":
    build()
