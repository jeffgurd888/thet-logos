#!/usr/bin/env python3
"""Emit arXiv-ready .tex source for the order-one-22 paper (v2).
Wrapped paragraph continuations are merged back into prose; only true
math displays become \\[..\\]; explicit LaTeX for each math display."""
import re, os

SRC = os.path.expanduser("~/workspace/thet-logos/whitepaper/order-one-22-paper-draft.md")
OUTDIR = os.path.expanduser("~/workspace/your_files/thet-logos-paper")
os.makedirs(OUTDIR, exist_ok=True)
TEX = os.path.join(OUTDIR, "order-one-22-classification.tex")

text = open(SRC).read().splitlines()
lines = [l for l in text if not l.startswith("%")]

MATHDISP = re.compile(
    r"=|:<->|<->|->|\(\+\)|diag\(|\(i,j\)|M_32|M_3\(C\)|gamma_F|^A_F|W22"
    r"|Module\.|D in|^\([ivx]+\)|nu_|ebar|^d/d|^\([1-6]\)|^H_[LR]"
)

def is_section_header(s):
    return re.match(r"^(\d+)\.\s+[A-Z]", s)

blocks = []
i, n = 0, len(lines)
while i < n:
    l = lines[i]; s = l.strip()
    if not s: i += 1; continue
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
        blocks.append(("abstract", " ".join(ps))); continue
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
        blocks.append(("appendix_head", (m.group(1), m.group(2))))
        i += 1; entries = []
        while i < n:
            if re.search(r"dirs22\s+\d+:", lines[i]):
                spans = [mm for mm in re.finditer(r"dirs22\s+(\d+):", lines[i])]
                for a, b in zip(spans, spans[1:] + [None]):
                    num = int(a.group(1))
                    rest = lines[i][a.end(): b.start() if b else len(lines[i])].strip()
                    entries.append((num, rest))
                i += 1
            elif lines[i].strip().startswith("SM directions") or lines[i].strip().startswith("Exotic directions"):
                blocks.append(("appendix_note", lines[i].strip())); i += 1
            elif not lines[i].strip():
                i += 1
            else:
                para = [lines[i].strip()]; i += 1
                while i < n and lines[i].strip() and not re.search(r"dirs22\s+\d+:", lines[i]):
                    para.append(lines[i].strip()); i += 1
                blocks.append(("para", " ".join(para)))
        blocks.append(("appendix_entries", sorted(entries)))
        continue
    m = re.match(r"^(\d+\.\d+)\.\s+(.*)$", s)
    if m: blocks.append(("subsection", (m.group(1), m.group(2)))); i += 1; continue
    m = re.match(r"^(\d+)\.\s+(.*)$", s)
    if m and s[0].isdigit() and m.group(2)[0].isupper():
        blocks.append(("section", (m.group(1), m.group(2)))); i += 1; continue
    if s == "ACKNOWLEDGMENTS":
        blocks.append(("section", ("", "ACKNOWLEDGMENTS"))); i += 1; continue
    if l.startswith("    ") and s:
        d = []
        while i < n and lines[i].startswith("    ") and lines[i].strip():
            d.append(lines[i].strip()); i += 1
        if MATHDISP.search(d[0]):
            blocks.append(("display", d))
        else:
            # wrapped paragraph continuation: merge into previous para
            extra = " ".join(d)
            if blocks and blocks[-1][0] == "para":
                blocks[-1] = ("para", blocks[-1][1] + " " + extra)
            elif blocks and blocks[-1][0] == "display":
                blocks.append(("para", extra))
            else:
                blocks.append(("para", extra))
        continue
    para = [s]; i += 1
    while i < n and lines[i].strip() and not lines[i].startswith("    ") \
            and not is_section_header(lines[i].strip()) \
            and not re.match(r"^(\d+\.\d+)\.\s+", lines[i].strip()) \
            and lines[i].strip() not in ("BIBLIOGRAPHY", "ACKNOWLEDGMENTS") \
            and not lines[i].strip().startswith("APPENDIX"):
        para.append(lines[i].strip()); i += 1
    blocks.append(("para", " ".join(para)))

# ------------------------------------------------------------- LaTeX ---
CODE_RE = re.compile(r"`([^`]+)`")
SNAKE_RE = re.compile(r"\b([a-zA-Z][a-zA-Z0-9]*_[a-zA-Z0-9_]+)\b")

def esc_text(t):
    for a, b in [("\\", "\\textbackslash{}"), ("{", "\\{"), ("}", "\\}"),
                 ("_", "\\_"), ("%", "\\%"), ("&", "\\&"), ("$", "\\$"),
                 ("#", "\\#"), ("^", "\\^{}"), ("~", "\\~{}")]:
        t = t.replace(a, b)
    return t

MATH = [
    (r"M_\{32\}\(C\)", r"$M_{32}(\mathbb{C})$"),
    (r"M_32\(C\)", r"$M_{32}(\mathbb{C})$"),
    (r"M_3\(C\)", r"$M_3(\mathbb{C})$"),
    (r"C\^32", r"$\mathbb{C}^{32}$"),
    (r"A_F", r"$A_F$"),
    (r"H_L\^c", r"$H_L^c$"), (r"H_R\^c", r"$H_R^c$"),
    (r"H_F", r"$H_F$"), (r"H_L", r"$H_L$"), (r"H_R", r"$H_R$"),
    (r"D_F", r"$D_F$"),
    (r"gamma_F", r"$\gamma_F$"),
    (r"W_\{22\}", r"$W_{22}$"),
    (r"W22", r"$W_{22}$"),
    (r"b\^o", r"$b^o$"),
    (r"nu_L", r"$\nu_L$"), (r"nu_R", r"$\nu_R$"),
    (r"ebar_R", r"$\bar{e}_R$"),
    (r"u_L", r"$u_L$"), (r"d_R", r"$d_R$"), (r"d_L", r"$d_L$"),
    (r"u_R", r"$u_R$"), (r"e_L", r"$e_L$"), (r"e_R", r"$e_R$"),
    (r"dim_R", r"$\dim_{\mathbb{R}}$"),
    (r"span_R", r"$\operatorname{span}_{\mathbb{R}}$"),
    (r"finrank R", r"$\operatorname{finrank}_{\mathbb{R}}$"),
    (r"Submodule\.span R", r"$\operatorname{span}_{\mathbb{R}}$"),
    (r"lambda_j", r"$\lambda_j$"), (r"lambda_i", r"$\lambda_i$"),
    (r"\(lambda\)", r"$(\lambda)$"), (r"\(mu\)", r"$(\mu)$"),
    (r"mu_j", r"$\mu_j$"), (r"mu_i", r"$\mu_i$"),
    (r"M x F", r"$M\times F$"),
    (r"32x32", r"$32\times 32$"),
    (r"D/Lambda", r"$D/\Lambda$"),
    (r"yNu", r"$y_\nu$"), (r"yE", r"$y_E$"), (r"yU", r"$y_U$"),
    (r"yD", r"$y_D$"), (r"yR", r"$y_R$"),
    (r"(?<![\w])C(?![\w])", r"$\mathbb{C}$"),
    (r"(?<![\w])H(?![\w])", r"$\mathbb{H}$"),
]
MATH_RE = [(re.compile(p), r_) for p, r_ in MATH]

def render_math_token(tok):
    for pat, rep in MATH_RE:
        if pat.fullmatch(tok):
            return rep
    return "$%s$" % tok

def L(t):
    mh = []
    def subm(m):
        k = "\x00M%d\x00" % len(mh); mh.append(m.group(0)); return k
    def subcode(m):
        k = "\x00C%d\x00" % len(mh); mh.append("\x00CODE\x00" + m.group(1)); return k
    def subsnake(m):
        k = "\x00C%d\x00" % len(mh); mh.append("\x00SNAKE\x00" + m.group(1)); return k
    t = CODE_RE.sub(subcode, t)
    for pat, _ in MATH_RE:
        t = pat.sub(subm, t)
    t = SNAKE_RE.sub(subsnake, t)
    t = t.replace(":<->", " \x00IFF\x00 ").replace("<->", " \x00LRA\x00 ")
    t = t.replace("->", " \x00TO\x00 ").replace("(+)", " \x00OPL\x00 ")
    t = t.replace("92 - 70 = 22", "\x00EQ\x00").replace("--", "---")
    t = t.replace("...", "\\dots ").replace("∎", "\x00QED\x00")
    t = esc_text(t)
    t = t.replace("\x00QED\x00", "$\\square$")
    t = t.replace("\x00IFF\x00", "$\\iff$").replace("\x00LRA\x00", "$\\leftrightarrow$")
    t = t.replace("\x00TO\x00", "$\\to$").replace("\x00OPL\x00", "$\\oplus$")
    t = t.replace("\x00EQ\x00", "$92-70=22$")
    for k, tok in enumerate(mh):
        ph = "\x00M%d\x00" % k if not tok.startswith("\x00") else "\x00C%d\x00" % k
        if tok.startswith("\x00CODE\x00"):
            t = t.replace("\x00C%d\x00" % k, "\\texttt{%s}" % esc_text(tok[6:]))
        elif tok.startswith("\x00SNAKE\x00"):
            t = t.replace("\x00C%d\x00" % k, "\\texttt{%s}" % esc_text(tok[7:]))
        else:
            t = t.replace("\x00M%d\x00" % k, render_math_token(tok))
    t = re.sub(r"^(Hypothesis H \([^)]*\)\.|Theorem \([^)]*\)\.|Proof\.|Corollary\.|Explicit non-claims\.)",
               r"{\\bf \1}", t)
    return t

# explicit display overrides keyed by first-line signature
def display_latex(d):
    first = d[0]
    if first.startswith("A_F = C (+)"):
        return "\\[\nA_F = \\mathbb{C} \\oplus \\mathbb{H} \\oplus M_3(\\mathbb{C}),\n\\]"
    if first.startswith("H_L:"):
        return ("\\begin{quote}\n$H_L$: indices 0--7, \\quad $H_R$: indices 8--15, \\\\\n"
                "$H_L^c$: indices 16--23, \\quad $H_R^c$: indices 24--31,\n\\end{quote}")
    if first.startswith("gamma_F = diag"):
        return ("\\[\n\\gamma_F = \\operatorname{diag}"
                "(+1{\\times}8,\\, -1{\\times}8,\\, -1{\\times}8,\\, +1{\\times}8),\n\\]")
    if first.startswith("OrderOneHolds D"):
        return ("\\[\n\\mathrm{OrderOneHolds}\\,D \\iff \\forall a,b,\\ "
                "[[D,\\mathrm{smGen}\\,a],\\mathrm{smGenOp}\\,b] = 0,\n\\]")
    if first.startswith("W22 = {"):
        return ("\\[\nW_{22} = \\{\\,D \\in M_{32}(\\mathbb{C}) : "
                "\\mathrm{IsW22}\\,D \\,\\},\n\\]")
    if first.startswith("(i)"):
        rows = [
            (r"(i) $\mathrm{OrderOneHolds}\,D$ (144-pair first-order condition);"),
            (r"(ii) $[D,\mathrm{cfMat}] = 0$ (commutant of a fixed color-flavor matrix);"),
            (r"(iii) $D^* = D$ (self-adjointness);"),
            (r"(iv) $D$ is $J$-compatible (compatibility with the real structure);"),
            (r"(v) $\gamma_F D + D\gamma_F = 0$ (grading-oddness)."),
        ]
        return "\\begin{quote}\n" + "\\\\\n".join(rows) + "\n\\end{quote}"
    if first.startswith("d/d Re(yX)"):
        return ("\\[\n\\frac{d}{d\\operatorname{Re}(y_X)},\\ "
                "\\frac{d}{d\\operatorname{Im}(y_X)},\\quad "
                "X \\in \\{\\mathrm{Nu}, \\mathrm{E}, \\mathrm{U}, "
                "\\mathrm{D}, \\mathrm{R}\\},\n\\]")
    if first.startswith("(1) nu_L"):
        rows = [
            r"(1) $\nu_L \leftrightarrow e_R$ (lepton flavor-violating);",
            r"(2) $e_L \leftrightarrow \nu_R$ (lepton flavor-violating);",
            r"(3) $u_L \leftrightarrow d_R$ (color-universal quark flavor-violating);",
            r"(4) $d_L \leftrightarrow u_R$ (color-universal quark flavor-violating);",
            r"(5) $\nu_R \leftrightarrow \bar{e}_R$ (Majorana-type, particle-antiparticle);",
            r"(6) $e_R \leftrightarrow \bar{e}_R$ (particle-antiparticle).",
        ]
        return "\\begin{quote}\n" + "\\\\\n".join(rows) + "\n\\end{quote}"
    if first.startswith("Module.finrank"):
        return "\\[\n\\operatorname{finrank}_{\\mathbb{R}}\\,W_{22} = 22.\n\\]"
    if first.startswith("D in Submodule"):
        return ("\\[\nD \\in \\operatorname{span}_{\\mathbb{R}}"
                "(\\mathrm{range}\\,\\mathrm{dirs22});\n\\]")
    if first.startswith("[[D, A], B]"):
        return ("\\[\n[[D,A],B](i,j) = D(i,j)\\,"
                "(\\lambda_j - \\lambda_i)(\\mu_j - \\mu_i),\n\\]")
    # fallback: prose quote
    return "\\begin{quote}\n" + " ".join(esc_text(x) for x in d) + "\n\\end{quote}"

out = []
out.append(r"""\documentclass[11pt,a4paper]{article}
\usepackage{amsmath,amssymb,amsthm}
\usepackage[margin=2.5cm]{geometry}
\usepackage[colorlinks=true,linkcolor=blue,citecolor=blue,urlcolor=blue]{hyperref}
\setlength{\parskip}{4pt}
\setlength{\parindent}{14pt}
\title{A 22-direction classification of the order-one commutant\\
in the Standard Model finite spectral triple, formalized in Lean~4}
\author{Jeffrey Michael Gurd\\ Nexus Research (independent researcher)\\
\href{mailto:jeffrey@nexus-research.org}{jeffrey@nexus-research.org}}
\date{September 2026}
\begin{document}
\maketitle
""")

for kind, pay in blocks:
    if kind in ("title", "author"):
        continue
    elif kind == "abstract":
        out.append("\\begin{abstract}\n" + L(pay) + "\n\\end{abstract}\n")
    elif kind == "section":
        num, head = pay
        out.append("\n\\section*{%s}\n" % esc_text(head))
    elif kind == "subsection":
        num, head = pay
        out.append("\n\\subsection*{%s}\n" % esc_text(head))
    elif kind == "para":
        out.append(L(pay) + "\n")
    elif kind == "display":
        out.append(display_latex(pay) + "\n")
    elif kind == "bib":
        out.append("\n\\begin{thebibliography}{99}\n")
        for num, entry in pay:
            e = L(entry)
            e = re.sub(r"arXiv:([0-9A-Za-z]+(?:[.\-/][0-9A-Za-z]+)+)",
                       r"arXiv:\\href{https://arxiv.org/abs/\g<1>}{\g<1>}", e)
            e = re.sub(r"(?<![{/])https://[^\s,}]+", r"\\url{\g<0>}", e)
            out.append("\\bibitem{b%s}\n%s\n" % (num, e))
        out.append("\\end{thebibliography}\n")
    elif kind == "appendix_head":
        letter, head = pay
        out.append("\n\\appendix\n\\section*{%s}\n" % esc_text("APPENDIX " + letter + ". " + head))
    elif kind == "appendix_note":
        out.append("\n\\noindent{\\bf %s}\n" % esc_text(pay))
    elif kind == "appendix_entries":
        out.append("\\begin{description}\n")
        for k, v in pay:
            if "=" in v:
                name, desc = v.split("=", 1)
                out.append("\\item[\\texttt{dirs22 %d: %s}] %s\n" %
                           (k, esc_text(name.strip()), L(desc.strip())))
            else:
                parts = v.split(None, 1)
                name, desc = parts[0], (parts[1] if len(parts) > 1 else "")
                out.append("\\item[\\texttt{dirs22 %d: %s}] %s\n" %
                           (k, esc_text(name), L(desc)))
        out.append("\\end{description}\n")

out.append("\\end{document}\n")
open(TEX, "w").write("".join(out))
print("TEX written:", TEX, os.path.getsize(TEX), "bytes")
