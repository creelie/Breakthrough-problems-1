#!/usr/bin/env python3
"""Writes the TikZ sources of the two figures of the paper into preprint/figures/.

  blowup.tex       the random blow-up T(R_7, n), drawn in 3D by an orthographic projection
                   computed here (blocks are short cylinders, arcs of R_7 are lifted curves)
  convergence.tex  rho_R(R_d), the lower bound e^{1/d}((d+1)/(d-1))^m and the upper bound
                   e^{1/d} U_d of Theorem 1.5 for odd d from 3 to 61 (pgfplots)

    usage: python3 -I scripts/gen_figures.py
"""
import math
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FIG = os.path.join(ROOT, "preprint", "figures")

# ---------------------------------------------------------------- 3D projection
AZ, EL = math.radians(-24), math.radians(28)


def proj(x, y, z):
    """Orthographic view: rotate by AZ about the z axis, tilt by EL; returns (u, v, depth)."""
    xr = x * math.cos(AZ) - y * math.sin(AZ)
    yr = x * math.sin(AZ) + y * math.cos(AZ)
    u = xr
    v = yr * math.sin(EL) + z * math.cos(EL)
    depth = yr * math.cos(EL) - z * math.sin(EL)  # larger = farther from the viewer
    return u, v, depth


def p2(x, y, z):
    u, v, _ = proj(x, y, z)
    return f"({u:.3f},{v:.3f})"


def ellipse_path(cx, cy, z, r, n=48):
    pts = [p2(cx + r * math.cos(2 * math.pi * k / n), cy + r * math.sin(2 * math.pi * k / n), z)
           for k in range(n)]
    return " -- ".join(pts) + " -- cycle"


def cylinder(cx, cy, r, h, col, n=60):
    """A short cylinder: the side band facing the viewer, then the top disc."""
    out = []
    best = []
    for k in range(4 * n):
        a = 2 * math.pi * k / (4 * n)
        _, _, dep = proj(math.cos(a), math.sin(a), 0)
        best.append((dep, a))
    a0 = min(best)[1]  # the horizontal direction nearest to the viewer
    angles = [a0 - math.pi / 2 + math.pi * k / n for k in range(n + 1)]
    bot = [p2(cx + r * math.cos(a), cy + r * math.sin(a), 0) for a in angles]
    top = [p2(cx + r * math.cos(a), cy + r * math.sin(a), h) for a in reversed(angles)]
    out.append(f"\\fill[{col}!55!black,opacity=0.9] " + " -- ".join(bot + top) + " -- cycle;")
    out.append(f"\\shade[left color={col}!70!black,right color={col}!35,opacity=0.85] "
               + " -- ".join(bot + top) + " -- cycle;")
    out.append(f"\\draw[{col}!40!black,line width=0.35pt] " + " -- ".join(bot) + ";")
    out.append(f"\\shade[inner color={col}!12,outer color={col}!45,draw={col}!45!black,line width=0.4pt] "
               + ellipse_path(cx, cy, h, r) + ";")
    return out


def blowup():
    """R_7 blown up: block T_j beats T_{j+1}, T_{j+2}, T_{j+3}. The three arcs out of T_1 are
    coloured, the other eighteen are grey."""
    d, R, rad, h = 7, 3.2, 0.66, 0.26
    cols = {1: "arcA", 2: "arcB", 3: "arcC"}
    start = math.radians(-120)  # T_1 sits at the front left
    centers = []
    for j in range(d):
        a = start + 2 * math.pi * j / d
        centers.append((R * math.cos(a), R * math.sin(a)))
    L = []
    L.append(r"\documentclass[tikz,border=6pt]{standalone}")
    L.append(r"\usepackage{amsmath,amssymb}")
    L.append(r"\usetikzlibrary{arrows.meta}")
    L.append(r"\definecolor{blk}{RGB}{58,96,160}\definecolor{arcA}{RGB}{31,94,165}"
             r"\definecolor{arcB}{RGB}{33,138,110}\definecolor{arcC}{RGB}{214,96,33}")
    L.append(r"\begin{document}")
    L.append(r"\begin{tikzpicture}[x=1cm,y=1cm,line cap=round,line join=round]")
    L.append(r"\shade[inner color=black!2,outer color=black!12] " + ellipse_path(0, 0, -0.02, 4.6, 96) + ";")
    L.append(r"\draw[black!18,line width=0.4pt] " + ellipse_path(0, 0, -0.02, 4.6, 96) + ";")
    items = []
    for j in range(d):
        cx, cy = centers[j]
        items.append((proj(cx, cy, 0)[2], "block", j))
        for r in (1, 2, 3):
            k = (j + r) % d
            mx, my = (cx + centers[k][0]) / 2, (cy + centers[k][1]) / 2
            items.append((proj(mx, my, 0)[2] + 0.01, "arc", (j, k, r)))
    items.sort(key=lambda t: -t[0])  # back to front
    for _, kind, data in items:
        if kind == "block":
            j = data
            cx, cy = centers[j]
            L.extend(cylinder(cx, cy, rad, h, "blk"))
            # a few vertices of T_j and some of its arcs, on the top face
            pts = [(cx + 0.36 * math.cos(2 * math.pi * t / 5 + j), cy + 0.36 * math.sin(2 * math.pi * t / 5 + j))
                   for t in range(5)]
            for a in range(5):
                for b in range(a + 1, 5):
                    if (a * 7 + b * 3 + j) % 3 != 0:
                        L.append(f"\\draw[black!40,line width=0.25pt] {p2(*pts[a], h)} -- {p2(*pts[b], h)};")
            for (px, py) in pts:
                L.append(f"\\fill[white] {p2(px, py, h)} circle (1.5pt);")
                L.append(f"\\fill[blk!80!black] {p2(px, py, h)} circle (1.05pt);")
        else:
            j, k, r = data
            hot = j == 0
            (x0, y0), (x1, y1) = centers[j], centers[k]
            dx, dy = x1 - x0, y1 - y0
            n = math.hypot(dx, dy)
            sx, sy = x0 + rad * 0.82 * dx / n, y0 + rad * 0.82 * dy / n
            ex, ey = x1 - rad * 0.82 * dx / n, y1 - rad * 0.82 * dy / n
            lift = (0.55 + 0.55 * r) if hot else (0.35 + 0.35 * r)
            c1 = (x0 + dx / 3 - 0.10 * r * x0, y0 + dy / 3 - 0.10 * r * y0, h + lift)
            c2 = (x0 + 2 * dx / 3 - 0.10 * r * x1, y0 + 2 * dy / 3 - 0.10 * r * y1, h + lift)
            path = f"{p2(sx, sy, h)} .. controls {p2(*c1)} and {p2(*c2)} .. {p2(ex, ey, h)}"
            if hot:
                L.append(f"\\draw[white,line width=3pt] {path};")
                L.append(f"\\draw[{cols[r]},line width=1.3pt,-{{Latex[length=2.9mm,width=2.1mm]}}] {path};")
            else:
                L.append(f"\\draw[white,line width=1.8pt] {path};")
                L.append(f"\\draw[black!38,line width=0.6pt,-{{Latex[length=1.8mm,width=1.3mm]}}] {path};")
    # labels last, so no arc covers them
    for j in range(d):
        cx, cy = centers[j]
        L.append(f"\\node[font=\\small,fill=white,fill opacity=0.85,text opacity=1,inner sep=1.2pt,rounded corners=1pt] "
                 f"at {p2(cx * 1.36, cy * 1.36, 0.05)} {{$T_{{{j + 1}}}$}};")
    lx, ly = 4.3, 2.75
    leg = [(1, r"$T_1\Rightarrow T_2$"), (2, r"$T_1\Rightarrow T_3$"), (3, r"$T_1\Rightarrow T_4$")]
    for i, (r, txt) in enumerate(leg):
        L.append(f"\\draw[{cols[r]},line width=1.3pt,-{{Latex[length=2.4mm,width=1.7mm]}}] ({lx:.2f},{ly - 0.42 * i:.2f}) -- ({lx + 0.7:.2f},{ly - 0.42 * i:.2f});")
        L.append(f"\\node[anchor=west,font=\\small] at ({lx + 0.78:.2f},{ly - 0.42 * i:.2f}) {{{txt}}};")
    L.append(f"\\draw[black!38,line width=0.6pt,-{{Latex[length=1.8mm,width=1.3mm]}}] ({lx:.2f},{ly - 1.26:.2f}) -- ({lx + 0.7:.2f},{ly - 1.26:.2f});")
    L.append(f"\\node[anchor=west,font=\\small] at ({lx + 0.78:.2f},{ly - 1.26:.2f}) {{other arcs of $R_7$}};")
    L.append(r"\end{tikzpicture}")
    L.append(r"\end{document}")
    return "\n".join(L) + "\n"


# ---------------------------------------------------------------- convergence plot
def rho_T_cyclic(d):
    re, im = 1, 0
    for _ in range(d):
        re, im = re * d - im, re + im * d
    return ((d + 1) ** d + (d - 1) ** d) / (2 * re)


def U(d):
    C, s = d * (d - 1) / 2, 1 / math.tan(math.pi / (2 * d)) ** 2
    q = int(C // s)
    r = C - q * s
    phi = lambda x: math.log((d * d + x) / (d * d - x))
    return math.exp(q * phi(s) + phi(r))


def convergence():
    ds = list(range(3, 62, 2))
    low = [(d, math.exp(1 / d) * ((d + 1) / (d - 1)) ** ((d - 1) // 2)) for d in ds]
    up = [(d, math.exp(1 / d) * U(d)) for d in ds]
    cyc = [(d, math.exp(1 / d) * rho_T_cyclic(d)) for d in ds]
    c = math.cosh(1) / math.cos(1)
    lim_u = (math.pi ** 2 + 4) * (3 * math.pi ** 2 - 8) / ((math.pi ** 2 - 4) * (math.pi ** 2 + 8))
    co = lambda pts: " ".join(f"({d},{v:.6f})" for d, v in pts)
    return rf"""\documentclass[border=6pt]{{standalone}}
\usepackage{{amsmath,amssymb}}
\usepackage{{pgfplots}}
\pgfplotsset{{compat=1.17}}
\usepgfplotslibrary{{fillbetween}}
\definecolor{{arcA}}{{RGB}}{{31,94,165}}\definecolor{{arcC}}{{RGB}}{{214,96,33}}\definecolor{{band}}{{RGB}}{{200,214,232}}
\begin{{document}}
\begin{{tikzpicture}}
\begin{{axis}}[width=13.5cm,height=7.4cm,xmin=1,xmax=63,ymin=2.70,ymax=2.875,
  xlabel={{$d$}},ylabel={{$\rho_{{\mathcal R}}$}},xtick={{3,11,21,31,41,51,61}},
  ytick={{2.70,2.72,2.74,2.76,2.78,2.80,2.82,2.84,2.86}},yticklabel style={{/pgf/number format/fixed,/pgf/number format/precision=2}},
  tick label style={{font=\small}},label style={{font=\small}},axis line style={{black!60}},
  grid=major,grid style={{black!8}},legend style={{font=\small,draw=black!20,fill=white,fill opacity=0.9,text opacity=1,at={{(0.98,0.52)}},anchor=east}},
  legend cell align=left]
\addplot[name path=up,draw=arcA!60,line width=0.6pt] coordinates {{{co(up)}}};
\addplot[name path=low,draw=arcA!60,line width=0.6pt] coordinates {{{co(low)}}};
\addplot[band,fill opacity=0.55] fill between[of=up and low];
\addplot[black!70,dashed,line width=0.7pt,domain=1:63,samples=2] {{{c:.10f}}};
\addplot[black!45,dotted,line width=0.8pt,domain=1:63,samples=2] {{{math.e:.10f}}};
\addplot[only marks,mark=*,mark size=1.6pt,arcC,mark options={{draw=arcC!60!black,line width=0.3pt}}] coordinates {{{co(cyc)}}};
\legend{{,,regular tournaments (Theorem 1.5),$\cosh 1/\cos 1$,$e$,cyclic $R_d$}}
\node[font=\scriptsize,anchor=south east,black!70] at (axis cs:62,2.8575) {{$\lim e^{{1/d}}U_d={lim_u:.6f}$}};
\end{{axis}}
\end{{tikzpicture}}
\end{{document}}
"""


def main():
    os.makedirs(FIG, exist_ok=True)
    with open(os.path.join(FIG, "blowup.tex"), "w") as f:
        f.write(blowup())
    with open(os.path.join(FIG, "convergence.tex"), "w") as f:
        f.write(convergence())
    print("wrote", os.path.join(FIG, "blowup.tex"), "and convergence.tex")


if __name__ == "__main__":
    main()
