import json,re,sys
sys.argv=['x']; exec(open('mkpre.py').read())
def locf(n):
    m,l=L[n].split(':'); m=re.search(r'LeanSvg\.([\w.]+)',m).group(1).replace('.','/'); return f'{m}.lean:{l}'
ex={}
for n in sorted(real):
    if F.get(n): ex.setdefault(F[n],n)
rows=[]
for f in sorted(reach,key=lambda f:-reach[f]):
    e=ex.get(f)
    rows.append(f"| {f} | {direct.get(f,0)} | {reach[f]} | `{short(e)}` {locf(e)} — {r[e][1][:70].replace('|','/')} |".replace('\n',' '))
nreal=len(real)
greedy=json.load(open('greedy.json'))
gl='\n'.join(f"{i+1}. {f} — +{g} (cumulative {c} of {nreal})" for i,(f,g,c) in enumerate(greedy[:12]))
def st(n):
    return ('compiles' if F.get(n) is None else 'blocked: '+F[n].split(' (')[0]+' — '+re.sub(r'\s+',' ',r[n][1])[:60].replace('|','/')) + f" [{locf(n)}]; {len(size(n))} defs below"
def line(d,n): return '  '*d+f"- `{short(n)}` — {st(n)}"
tree=[line(0,'LeanSvg.render'),line(1,'LeanSvg.renderWithWarnings')]
def add(d,names):
    for c in names:
        if 'LeanSvg.'+c in F: tree.append(line(d,'LeanSvg.'+c))
for s in ['Xml.parse','Svg.interpretWith','Marker.expand','RootFit.apply','Render.canvasSetup','Render.bandCount','Render.renderRgba','Render.renderBands','Png.encode']:
    add(2,[s])
    if s=='Render.renderRgba':
        add(3,['Render.renderNodes','Canvas.new','Canvas.toRgbaBytes'])
        add(3,['Render.drawShape'])
        add(4,['Raster.rasterize','Canvas.fillMask','Mat.mul','flatten','strokePoly','dashPath','Clip.resolve','Grad.build'])
    if s=='Png.encode': add(3,['Png.zlibStoredRows','Png.crc32Range','Png.zlibLen','Png.chunk','Png.be32'])
    if s=='Xml.parse': add(3,['Xml.resolveNs','Xml.decodeText','Xml.decodeValue','Bytes.skipWhile','Bytes.findByte','Bytes.skipWs','Bytes.startsWith',"Bytes.at'",'Bytes.isNameChar'])
    if s=='Svg.interpretWith': add(3,['Svg.strokeBoxOf','Svg.parseHexColor','Css.parseCompound','Svg.resolveRootSize'])
tr='\n'.join(tree)
need=clo(root)
okl=', '.join(f'`{x}`' for x in json.load(open('rs.json'))['ok'])
nok=sum(1 for n in real if F.get(n) is None)
md=open('tmpl.md').read()
for k,v in dict(ROWS='\n'.join(rows),TREE=tr,GREEDY=gl,NNEED=str(len(need)),NOK=str(nok),NREAL=str(nreal),OKL=okl).items(): md=md.replace('@@'+k+'@@',v)
open('LEANSVG_DEPTH.md','w').write(md); print(len(md))
