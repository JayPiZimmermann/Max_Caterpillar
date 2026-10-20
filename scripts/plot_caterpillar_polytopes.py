#!/usr/bin/env python3
"""Reproduce the N=4 geometry figures (requires numpy and matplotlib)."""
from itertools import permutations, product
from pathlib import Path
import json
import sys
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.backends.backend_pdf import PdfPages
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from mpl_toolkits.mplot3d import proj3d

OUT = Path(__file__).resolve().parents[1] / 'paper' / 'figures'
E = np.vstack([np.zeros(3), np.eye(3)]).astype(int)
COLORS = ['#167dba', '#df8524']
HEAD = '#a12b78'
APEX = '#e49b21'

def description(pi, S):
    edges = [(pi[max([0] + [i for i in S if i < j])+1], pi[j+1]) for j in (1, 2)]
    h = E[pi[max(S)+1]] - E[pi[0]]
    return h, edges

def normalize(h, edges):
    h = h.copy()
    for i, j in edges:
        if i > j:
            h += E[i]-E[j]
    return h, sorted((min(i,j), max(i,j)) for i,j in edges)

def vertices(h, edges):
    a,b = [E[i]-E[j] for i,j in edges]
    return np.array([np.zeros(3), h, h+a, h+a+b, h+b])

def screen_label(ax, point, label, color, offset, fontsize=20):
    x, y, _ = proj3d.proj_transform(*point, ax.get_proj())
    ax.annotate(label, (x,y), xytext=offset, textcoords='offset points',
                ha='center', va='center', fontsize=fontsize, color=color,
                bbox=dict(facecolor='white', edgecolor='none', alpha=.9, pad=.4),
                zorder=50)

def arrow(ax, start, vector, color, label=None, fontsize=9, label_reference=None):
    if getattr(ax, '_caterpillar_presentation', False):
        ax.plot(*np.array([start, start+vector]).T, color=color,
                linewidth=3.2, solid_capstyle='round', zorder=5)
        tail = proj3d.proj_transform(*(start+.40*vector), ax.get_proj())[:2]
        tip = proj3d.proj_transform(*(start+.55*vector), ax.get_proj())[:2]
        ax.annotate('', xy=tip, xytext=tail,
                    arrowprops=dict(arrowstyle='->', color=color, lw=3.2,
                                    mutation_scale=23, shrinkA=0, shrinkB=0),
                    zorder=6)
    else:
        ax.quiver(*start, *vector, color=color, linewidth=3.2, arrow_length_ratio=.13)
    if label and fontsize >= 20:
        projected = [proj3d.proj_transform(*p, ax.get_proj())[:2]
                     for p in (start, start+vector)]
        delta = np.subtract(projected[1], projected[0])
        normal = np.array([-delta[1], delta[0]])
        normal /= np.linalg.norm(normal)
        if label_reference is not None:
            reference = np.array(proj3d.proj_transform(*label_reference, ax.get_proj())[:2])
            if np.dot(normal, np.mean(projected, axis=0)-reference) < 0:
                normal = -normal
        elif normal[1] < 0:
            normal = -normal
        screen_label(ax, start+.55*vector, label, color, normal*23, fontsize)
    elif label:
        ax.text(*(start+.55*vector+np.array([.03,.03,.06])), label,
                color=color, fontsize=fontsize)

def setup(ax, title):
    ax.set(xlim=(-1.15,1.5), ylim=(-1.15,1.5), zlim=(-1.15,1.5),
           xlabel='$p_1$', ylabel='$p_2$', zlabel='$p_3$', title=title)
    ax.set_box_aspect((1,1,1)); ax.view_init(elev=23, azim=34)
    ax.set_xticks([0,1]); ax.set_yticks([0,1]); ax.set_zticks([0,1])
    ax.tick_params(labelsize=7, pad=0)
    for axis in (ax.xaxis, ax.yaxis, ax.zaxis):
        axis.pane.fill = False
        axis.labelpad = 0

def anchors(ax, vectors=False, presentation=False):
    ax.scatter(*E.T, c='#555555', s=25, depthshade=False, zorder=20)
    for i,e in enumerate(E):
        if presentation and i == 0:
            continue
        label = '$0=e_0$' if i==0 else f'$e_{i}$'
        offset = np.array([.03,.03,.09 if presentation and i==3 else -.10])
        if presentation:
            screen_label(ax, e, label, '#555555', {1:(-12,-22),2:(19,-12),3:(19,7)}[i])
        else:
            ax.text(*(e+offset), label, fontsize=9, color='#555555')
        if vectors and i:
            arrow(ax, E[0], e, '#bbbbbb')

def poly(ax, h, edges, labels=True, presentation=False, edge_colors=None, head_label='$h$'):
    v = vertices(h, edges)
    faces = [v[[1,2,3,4]]] + [v[[0,i,j]] for i,j in [(1,2),(2,3),(3,4),(4,1)]]
    ax.add_collection3d(Poly3DCollection(faces, facecolors=['#84c5d8']+['#c0dae2']*4,
                                        edgecolors='#536775', linewidths=1.5, alpha=.19))
    ax.scatter(*v.T, s=25, c='#273f4b', depthshade=False, zorder=20)
    arrow(ax, E[0], h, HEAD, head_label if labels and not presentation else None)
    for k,(i,j) in enumerate(edges):
        color = edge_colors[tuple(sorted((i,j)))] if edge_colors else COLORS[k]
        arrow(ax, h, E[i]-E[j], color, rf'$\ell_{{{i}{j}}}$' if labels else None, fontsize=20 if presentation else 9, label_reference=v.mean(axis=0) if presentation else None)
    anchors(ax, presentation=presentation)

def presentation_axes(ax):
    """Three signed coordinate axes through the origin, without a box."""
    ax.set(xlim=(-1.05,1.08), ylim=(-1.05,1.08), zlim=(-1.05,1.08))
    ax.set_box_aspect((1,1,1), zoom=1.15)
    ax.set_axis_off()
    ax.computed_zorder = False
    ax._caterpillar_presentation = True
    for k, direction in enumerate(np.eye(3)):
        ax.plot(*np.array([-1.32*direction, 1.38*direction]).T,
                color='#999999', linewidth=2, zorder=0)
        tick_direction = np.eye(3)[(k+1)%3] * .045
        for sign in (-1,1):
            ax.plot(*np.array([sign*direction-tick_direction,
                              sign*direction+tick_direction]).T,
                    color='#999999', linewidth=2, zorder=0)

def landmarks(ax, h):
    ax.scatter(*E[0], s=135, c=APEX, edgecolors='white', linewidths=1,
               depthshade=False, zorder=30)
    ax.scatter(*h, s=135, c=HEAD, edgecolors='white', linewidths=1,
               depthshade=False, zorder=30)

def shared_legend(fig):
    handles = [Line2D([0],[0],marker='o',color='none',markerfacecolor=c,
                      markeredgecolor='white',markersize=12,label=t)
               for c,t in [(APEX,'Apex'),(HEAD,'Head corner')]]
    handles.extend([Line2D([0],[0],color=HEAD,lw=3.2,label='Head vector'),
                    Line2D([0],[0],color=COLORS[0],lw=3.2,label='Edge functions')])
    fig.legend(handles=handles,loc='upper center', ncol=4, frameon=False,
               fontsize=20, bbox_to_anchor=(.5,1), columnspacing=1.5)

def key(h, edges):
    return tuple(int(x) for x in h), tuple(edges)

def main():
    OUT.mkdir(exist_ok=True)
    records = {}
    rng = np.random.default_rng(7)
    for pi in permutations(range(4)):
        for S in [(1,), (2,), (1,2)]:
            h, edges = description(pi,S)
            hn, en = normalize(h,edges)
            # Exact equality of vertex sets checks normalization independently of rendering.
            assert set(map(tuple,vertices(h,edges))) == set(map(tuple,vertices(hn,en)))
            assert np.linalg.matrix_rank(np.column_stack([h]+[E[i]-E[j] for i,j in edges])) == 3
            x = rng.normal(size=(30,3))
            u = np.maximum(0, x@h + sum(np.maximum(0,x@(E[i]-E[j])) for i,j in edges))
            assert np.allclose(u, (x@vertices(h,edges).T).max(axis=1))
            rec = records.setdefault(key(hn,en), dict(apex=pi[0], h=hn.tolist(), edges=en, descriptions=[]))
            rec['descriptions'].append(dict(pi=pi,S=S))
    ordered = sorted(records.values(), key=lambda r:(r['apex'],r['edges'],r['h']))
    assert len(ordered)==36
    assert len({tuple(sorted(map(tuple,vertices(np.array(r['h']),r['edges'])))) for r in ordered})==36

    pi, S = (0,3,2,1), (1,2)
    h,edges = description(pi,S); hn,en = normalize(h,edges)
    fig = plt.figure(figsize=(15,5.5))
    edge_colors = {tuple(sorted(edge)): COLORS[0] for edge in edges}
    ax = fig.add_subplot(131,projection='3d'); setup(ax,'')
    presentation_axes(ax); anchors(ax,presentation=True)
    arrow(ax,E[0],h,HEAD)
    for i,j in edges:
        arrow(ax,E[j],E[i]-E[j],COLORS[0],rf'$\ell_{{{i}{j}}}$',fontsize=20,label_reference=E.mean(axis=0))
    landmarks(ax,h)
    ax = fig.add_subplot(132,projection='3d'); setup(ax,'')
    presentation_axes(ax)
    poly(ax,h,edges,presentation=True,edge_colors=edge_colors)
    landmarks(ax,h)
    ax = fig.add_subplot(133,projection='3d'); setup(ax,'')
    presentation_axes(ax)
    poly(ax,hn,en,presentation=True,edge_colors=edge_colors)
    landmarks(ax,hn)
    for xpos, title in [(.17,'(a) Coordinate differences'),(.50,'(b) Original description'),
                        (.83,'(c) Normalized description')]:
        fig.text(xpos,.035,title,ha='center',va='center',fontsize=20)
    shared_legend(fig)
    fig.subplots_adjust(left=.01,right=.99,bottom=.11,top=.88,wspace=0)
    for ext in (['pdf','png'] if '--preview' in sys.argv else ['pdf']):
        fig.savefig(OUT/f'caterpillar-normalization.{ext}',dpi=200)
    plt.close(fig)
    if '--atlas' not in sys.argv or '--figure-only' in sys.argv:
        print('Verified all descriptions; updated the three-panel figure.')
        return

    (OUT/'caterpillar-n4-data.json').write_text(json.dumps(ordered,indent=2)+'\n')
    with PdfPages(OUT/'caterpillar-n4-atlas.pdf') as pdf:
        for apex in range(4):
            fig = plt.figure(figsize=(12,12))
            group = [r for r in ordered if r['apex']==apex]
            assert len(group)==9
            for n,r in enumerate(group):
                ax=fig.add_subplot(3,3,n+1,projection='3d')
                title=f"h = {tuple(r['h'])};  L = "+', '.join(f'ℓ{i}{j}' for i,j in r['edges'])
                setup(ax,title); poly(ax,np.array(r['h']),r['edges'],False)
                ax.set(xlim=(-1.2,2.2), ylim=(-1.2,2.2), zlim=(-1.2,2.2))
                ax.set_xticks([-1,0,1,2]); ax.set_yticks([-1,0,1,2]); ax.set_zticks([-1,0,1,2])
                ax.title.set_fontsize(9)
            fig.suptitle(f'All normalized N=4 caterpillar polytopes — apex label {apex}',fontsize=16,y=.98)
            fig.text(.5,.025,'Coordinates (p₁,p₂,p₃) after restriction to x₀=0. Purple: h. Blue / orange: generators at h.\nGrey points: 0=e₀, e₁, e₂, e₃. Common axes and camera in every panel.',ha='center',fontsize=10)
            fig.subplots_adjust(left=.02,right=.97,bottom=.08,top=.92,wspace=.12,hspace=.16)
            pdf.savefig(fig)
            fig.savefig(OUT/f'caterpillar-n4-apex-{apex}.png',dpi=150)
            plt.close(fig)
    print('Verified 72 descriptions, 36 normalized descriptions, 36 distinct polytopes; wrote figures to', OUT)

if __name__ == '__main__':
    main()
