(()=>{"use strict";
const $=id=>document.getElementById(id);
let G=window.GRAPH;if(Array.isArray(G))G={target:G[0],words:G[1],dist:G[2],next:G[3],neighbors:G[4],freq:G[5]||[]};
if(!G||!G.words){$("details").textContent="Graph data missing — run export_site.py first.";return}
const {words,dist,next,neighbors,freq}=G,n=words.length,TAU=Math.PI*2,CH=13,MONO='"JetBrains Mono",ui-monospace,Menlo,Consolas,monospace';
const T=words.indexOf(G.target),idx=new Map(words.map((w,i)=>[w,i])),maxD=Math.max(...dist);
// ---------- colours ----------
const STOPS=["#5eead4","#86efac","#fde047","#fdba74","#fb7185","#c084fc"].map(h=>[1,3,5].map(k=>parseInt(h.substr(k,2),16)));
function ramp(t){t=Math.max(0,Math.min(1,t))*(STOPS.length-1);const k=Math.min(STOPS.length-2,Math.floor(t)),f=t-k;return"rgb("+STOPS[k].map((v,m)=>Math.round(v+(STOPS[k+1][m]-v)*f)).join(",")+")"}
const GRAY="#6b7287",AMBER="#ffb454",gcol=g=>g===0?GRAY:ramp((g-1)/Math.max(1,maxD-1));
// ---------- layout ----------
const X=new Float64Array(n),Y=new Float64Array(n),R=new Float64Array(n),A=new Float64Array(n),CX=new Float64Array(n),CY=new Float64Array(n);
const MODE=new Uint8Array(n),par=new Int32Array(n).fill(-1),dep=new Int32Array(n),grp=new Uint8Array(n);
const wt=new Float64Array(n),lo=new Float64Array(n),hi=new Float64Array(n),ang=new Float64Array(n);
for(let i=0;i<n;i++){dep[i]=Math.max(dist[i],0);par[i]=dist[i]>0?next[i]:-1;grp[i]=dist[i]>0?dist[i]:0}
let rings=[];
function place(root,mem,cx,cy,r1,gap,keep){
  const kids=new Map(mem.map(i=>[i,[]]));mem.forEach(i=>{if(i!==root)kids.get(par[i]).push(i)});
  const ord=mem.slice().sort((a,b)=>dep[a]-dep[b]),by=[];
  for(let k=ord.length-1;k>=0;k--){const i=ord[k],c=kids.get(i);wt[i]=c.length?c.reduce((s,j)=>s+wt[j],0):1}
  lo[root]=0;hi[root]=TAU;
  ord.forEach(i=>{let a=lo[i];kids.get(i).sort((p,q)=>words[p]<words[q]?-1:1).forEach(j=>{const sp=(hi[i]-lo[i])*wt[j]/wt[i];lo[j]=a;hi[j]=a+sp;a+=sp});ang[i]=(lo[i]+hi[i])/2;(by[dep[i]]=by[dep[i]]||[]).push(i)});
  X[root]=cx;Y[root]=cy;R[root]=0;CX[root]=cx;CY[root]=cy;MODE[root]=2;let prev=0;
  for(let d=1;d<by.length;d++){const ids=by[d];if(!ids)continue;const m=ids.length,Rd=Math.max(d===1?r1:prev+gap,m*CH*1.12/TAU),dl=CH/Rd;
    ids.sort((a,b)=>ang[a]-ang[b]);let bi=0,bg=-1;
    for(let k=0;k<m;k++){const g=m===1?TAU:(ang[ids[(k+1)%m]]-ang[ids[k]]+TAU)%TAU;if(g>bg){bg=g;bi=k}}
    const seq=[];for(let k=0;k<m;k++){const id=ids[(bi+1+k)%m];let a=ang[id];if(k&&a<seq[k-1][1])a+=TAU;while(k&&a<seq[k-1][1])a+=TAU;seq.push([id,a])}
    const bl=[];seq.forEach((s,k)=>{bl.push({s:s[1]-k*dl,n:1,k});while(bl.length>1&&bl[bl.length-2].s/bl[bl.length-2].n>bl[bl.length-1].s/bl[bl.length-1].n){const b=bl.pop();bl[bl.length-1].s+=b.s;bl[bl.length-1].n+=b.n}});
    const as=[];bl.forEach(b=>{for(let q=0;q<b.n;q++)as.push(b.s/b.n+as.length*dl)});
    const lim=as[0]+TAU-dl;for(let k=m-1;k>=0;k--)as[k]=Math.min(as[k],lim-(m-1-k)*dl);
    seq.forEach((s,k)=>{const i=s[0],a=as[k];A[i]=a;R[i]=Rd;CX[i]=cx;CY[i]=cy;X[i]=cx+Rd*Math.cos(a);Y[i]=cy+Rd*Math.sin(a);MODE[i]=0});
    if(keep)rings.push({d,r:Rd});prev=Rd}
  return prev+58}
const all=[...Array(n).keys()],reach=all.filter(i=>dist[i]>=0);
const MR=place(T,reach,0,0,100,72,true);
// stranded: components laid out as mini-trees, packed on shelves right of the disk
const seen=new Uint8Array(n),comps=[],iso=[];
all.filter(i=>dist[i]<0).forEach(s=>{if(seen[s])return;if(!neighbors[s].length){iso.push(s);seen[s]=1;return}
  const mem=[s],q=[s];seen[s]=1;while(q.length){const v=q.pop();neighbors[v].forEach(z=>{if(!seen[z]&&dist[z]<0){seen[z]=1;mem.push(z);q.push(z)}})}
  const hub=mem.reduce((a,b)=>neighbors[b].length>neighbors[a].length?b:a),bq=[hub],vis=new Set([hub]);dep[hub]=0;par[hub]=-1;
  for(let h=0;h<bq.length;h++){const v=bq[h];neighbors[v].forEach(z=>{if(!vis.has(z)){vis.add(z);dep[z]=dep[v]+1;par[z]=v;bq.push(z)}})}
  comps.push({hub,mem})});
comps.sort((a,b)=>b.mem.length-a.mem.length);
const SX=MR+450;let sx=SX,sy=-MR,rowH=0,zone={x0:SX,y0:-MR,x1:SX,y1:-MR};
comps.forEach(c=>{const b=place(c.hub,c.mem,0,0,52,60,false);if(sx+2*b>SX+2000){sx=SX;sy+=rowH+10;rowH=0}
  const ox=sx+b,oy=sy+b;c.mem.forEach(i=>{X[i]+=ox;Y[i]+=oy;CX[i]=ox;CY[i]=oy});sx+=2*b+10;rowH=Math.max(rowH,2*b);zone.x1=Math.max(zone.x1,sx);zone.y1=Math.max(zone.y1,sy+rowH)});
const gy=zone.y1+110;iso.forEach((i,k)=>{X[i]=SX+(k%14)*78;Y[i]=gy+Math.floor(k/14)*28;MODE[i]=1;R[i]=0;CX[i]=X[i];CY[i]=Y[i]});
zone.x1=Math.max(zone.x1,SX+14*78);zone.y1=gy+Math.ceil(iso.length/14)*28;
// per-node colour + label orientation
const COL=Array.from({length:n},(_,i)=>i===T?AMBER:gcol(grp[i])),LR=new Float64Array(n),LF=new Uint8Array(n);
for(let i=0;i<n;i++)if(MODE[i]===0){const f=Math.cos(A[i])<0;LF[i]=f?1:0;LR[i]=A[i]+(f?Math.PI:0)}
const groups=Array.from({length:maxD+1},()=>[]);for(let i=0;i<n;i++)if(i!==T)groups[grp[i]].push(i);
// ---------- state ----------
const cv=$("graph"),ctx=cv.getContext("2d"),stage=$("stage");
let W=1,H=1,dpr=1,s=.2,px=0,py=0,minS=.05,maxS=7,sel=-1,hov=-1,showAll=false,raf=0,anim=0,onPath=new Set(),nbs=new Set(),route=[];
const world={x0:-MR,y0:-MR,x1:zone.x1,y1:zone.y1};
const clampS=v=>Math.max(minS,Math.min(maxS,v));
function fit(b,pad=1.12){const bw=(b.x1-b.x0)*pad,bh=(b.y1-b.y0)*pad,ns=clampS(Math.min(W/bw,H/bh));return{s:ns,x:(b.x0+b.x1)/2,y:(b.y0+b.y1)/2}}
function jump(v){s=v.s;px=W/2-v.x*s;py=H/2-v.y*s;sched()}
function fly(v){const s0=s,x0=(W/2-px)/s,y0=(H/2-py)/s,t0=performance.now();cancelAnimationFrame(anim);
  (function step(now){const k=Math.min(1,(now-t0)/650),e=1-Math.pow(1-k,3);s=s0*Math.pow(v.s/s0,e);px=W/2-(x0+(v.x-x0)*e)*s;py=H/2-(y0+(v.y-y0)*e)*s;draw();if(k<1)anim=requestAnimationFrame(step)})(t0)}
const mainBox={x0:-MR,y0:-MR,x1:MR,y1:MR};
function resize(first){const r=stage.getBoundingClientRect();W=r.width;H=r.height;dpr=window.devicePixelRatio||1;cv.width=Math.round(W*dpr);cv.height=Math.round(H*dpr);cv.style.width=W+"px";cv.style.height=H+"px";minS=fit(world,1.05).s*.8;if(first)jump(fit(mainBox,1.04));else sched()}
function sched(){if(!raf)raf=requestAnimationFrame(draw)}
// ---------- drawing ----------
function link(i,j){const rm=(R[i]+R[j])/2,ai=R[i]?A[i]:A[j],aj=R[j]?A[j]:A[i],cx=CX[i],cy=CY[i];ctx.moveTo(X[i],Y[i]);ctx.bezierCurveTo(cx+rm*Math.cos(ai),cy+rm*Math.sin(ai),cx+rm*Math.cos(aj),cy+rm*Math.sin(aj),X[j],Y[j])}
function label(i,fs,alpha,forced){const sx=X[i]*s+px,sy=Y[i]*s+py,m=MODE[i],off=forced?9:Math.max(5,7*s);let c=1,sn=0;
  if(m===0){c=Math.cos(LR[i]);sn=Math.sin(LR[i])}ctx.setTransform(dpr*c,dpr*sn,-dpr*sn,dpr*c,dpr*sx,dpr*sy);
  ctx.globalAlpha=alpha;ctx.textBaseline="middle";ctx.font=`${forced||i===sel?800:700} ${fs}px ${MONO}`;
  let x=off,y=0;ctx.textAlign="left";if(m===0&&LF[i]){ctx.textAlign="right";x=-off}if(m===2){ctx.textAlign="center";x=0;y=-(off+fs*.4)}
  if(forced||s>.9){ctx.lineWidth=Math.max(2.5,fs*.28);ctx.lineJoin="round";ctx.strokeStyle="#0a0b10";ctx.strokeText(words[i],x,y)}
  ctx.fillStyle=forced?(i===sel?"#fff":"#f3f4fa"):COL[i];ctx.fillText(words[i],x,y)}
function txt(str,wx,wy,wsz,minPx,col,al="center"){const fs=Math.max(minPx,wsz*s);ctx.setTransform(dpr,0,0,dpr,0,0);ctx.font=`700 ${fs}px ${MONO}`;ctx.fillStyle=col;ctx.textAlign=al;ctx.textBaseline="middle";ctx.fillText(str,wx*s+px,wy*s+py)}
function draw(){raf=0;ctx.setTransform(dpr,0,0,dpr,0,0);ctx.globalAlpha=1;ctx.clearRect(0,0,W,H);
  const vx0=-px/s-60,vy0=-py/s-60,vx1=(W-px)/s+60,vy1=(H-py)/s+60,vis=i=>X[i]>vx0&&X[i]<vx1&&Y[i]>vy0&&Y[i]<vy1,hasSel=sel>=0;
  ctx.save();ctx.translate(px,py);ctx.scale(s,s);
  const gl=ctx.createRadialGradient(0,0,0,0,0,MR);gl.addColorStop(0,"rgba(255,180,84,.16)");gl.addColorStop(.35,"rgba(120,100,200,.05)");gl.addColorStop(1,"rgba(0,0,0,0)");ctx.fillStyle=gl;ctx.beginPath();ctx.arc(0,0,MR,0,TAU);ctx.fill();
  ctx.lineWidth=1/s;ctx.strokeStyle="rgba(255,255,255,.06)";rings.forEach(r=>{ctx.beginPath();ctx.arc(0,0,r.r,0,TAU);ctx.stroke()});
  ctx.strokeStyle="rgba(255,255,255,.1)";ctx.setLineDash([6/s,6/s]);ctx.strokeRect(zone.x0-60,zone.y0-100,zone.x1-zone.x0+120,zone.y1-zone.y0+160);ctx.setLineDash([]);
  if(showAll){ctx.beginPath();for(let i=0;i<n;i++)for(const j of neighbors[i])if(j>i&&(vis(i)||vis(j))){ctx.moveTo(X[i],Y[i]);ctx.lineTo(X[j],Y[j])}ctx.strokeStyle="rgba(170,180,220,.12)";ctx.lineWidth=.8/s;ctx.stroke()}
  const lw=Math.max(.6,1.1/s);ctx.lineCap="round";
  groups.forEach((ids,g)=>{if(!ids.length)return;ctx.beginPath();for(const i of ids){const p=par[i];if(p<0)continue;if((X[i]<vx0&&X[p]<vx0)||(X[i]>vx1&&X[p]>vx1)||(Y[i]<vy0&&Y[p]<vy0)||(Y[i]>vy1&&Y[p]>vy1))continue;link(p,i)}
    ctx.strokeStyle=gcol(g);ctx.globalAlpha=hasSel?.07:.38;ctx.lineWidth=lw;ctx.stroke()});
  ctx.globalAlpha=1;
  if(hasSel){ctx.beginPath();onPath.forEach(i=>{for(const j of neighbors[i])if(dist[j]===dist[i]-1&&dist[i]>0)link(i,j)});ctx.strokeStyle="#ffd25a";ctx.lineWidth=Math.max(1.6,2.2/s);ctx.globalAlpha=.95;ctx.stroke();
    ctx.beginPath();for(const j of neighbors[sel]){ctx.moveTo(X[sel],Y[sel]);ctx.lineTo(X[j],Y[j])}ctx.strokeStyle="#fff";ctx.globalAlpha=.55;ctx.lineWidth=Math.max(1,1.4/s);ctx.setLineDash([4/s,4/s]);ctx.stroke();ctx.setLineDash([]);ctx.globalAlpha=1}
  const dr=Math.max(2.5,1.7/s);
  groups.forEach((ids,g)=>{ctx.beginPath();for(const i of ids)if(vis(i)){ctx.moveTo(X[i]+dr,Y[i]);ctx.arc(X[i],Y[i],dr,0,TAU)}ctx.fillStyle=gcol(g);ctx.globalAlpha=hasSel?.25:1;ctx.fill()});ctx.globalAlpha=1;
  if(hasSel){const hl=new Set([...onPath,...nbs,sel]);ctx.beginPath();hl.forEach(i=>{ctx.moveTo(X[i]+dr*1.5,Y[i]);ctx.arc(X[i],Y[i],dr*1.5,0,TAU)});ctx.fillStyle="#ffd25a";ctx.fill();
    ctx.beginPath();ctx.arc(X[sel],Y[sel],dr*3,0,TAU);ctx.strokeStyle="#fff";ctx.lineWidth=Math.max(1.5,2/s);ctx.stroke()}
  // target
  ctx.beginPath();ctx.arc(X[T],Y[T],30,0,TAU);ctx.fillStyle=AMBER;ctx.shadowColor=AMBER;ctx.shadowBlur=30;ctx.fill();ctx.shadowBlur=0;
  ctx.restore();
  rings.forEach(r=>txt(r.d,0,-r.r,13,11,"rgba(190,198,225,.55)"));
  if(s>.3)txt("POOP",X[T],Y[T],15,10,"#1a1205");
  txt("CAN'T REACH POOP",(zone.x0+zone.x1)/2,zone.y0-60,34,12,"rgba(190,198,225,.6)");
  if(s>=.5){const fs=12*s;for(let i=0;i<n;i++){if(i===T||!vis(i))continue;const hl=hasSel&&(onPath.has(i)||nbs.has(i)||i===sel);label(i,fs,hasSel?(hl?1:.16):1,false)}}
  if(hasSel){const f=new Set([sel,...route,...nbs]);f.forEach(i=>{if(i!==T&&vis(i))label(i,Math.max(12*s,12),1,true)})}
  if(hov>=0&&hov!==sel&&hov!==T)label(hov,Math.max(12*s,12),1,true);
  ctx.setTransform(dpr,0,0,dpr,0,0);ctx.globalAlpha=1;$("zoom").textContent=Math.round(s*100)+"%"}
// ---------- paths / details ----------
function dag(st){const set=new Set([st]),q=[st];while(q.length){const v=q.shift();for(const z of neighbors[v])if(dist[z]===dist[v]-1&&!set.has(z)){set.add(z);q.push(z)}}return set}
function ladders(st,lim=10){if(dist[st]<0)return[];const out=[],path=[st];(function walk(v){if(out.length>=lim)return;if(v===T){out.push([...path]);return}
  for(const j of neighbors[v].filter(z=>dist[z]===dist[v]-1)){path.push(j);walk(j);path.pop();if(out.length>=lim)return}})(st);return out}
const chip=i=>`<button class="chip" data-w="${words[i]}" style="color:${COL[i]}">${words[i]}</button>`;
function details(){const b=$("details"),intro=$("intro");if(sel<0){b.innerHTML="";intro.style.display="";return}intro.style.display="none";
  const d=dist[sel],ns=neighbors[sel];let h=`<div class="hr"></div><div class="title"><span style="color:${COL[sel]}">${words[sel].toUpperCase()}</span><span class="pill ${d<0?"bad":""}">${d<0?"stranded":d+(d===1?" move":" moves")}</span></div><p class="muted">${ns.length} one-letter neighbour${ns.length===1?"":"s"}</p>`;
  if(d>=0){const ls=ladders(sel);h+=`<button id="frame" class="pri" style="width:100%">Frame the route to POOP</button><h2>Shortest ladders${ls.length>=10?" (first 10)":""}</h2>`;
    ls.forEach(p=>{h+='<div class="ladder">'+p.map((v,k)=>(k?"<i>→</i>":"")+`<button data-w="${words[v]}" style="color:${COL[v]}">${words[v]}</button>`).join("")+"</div>"})}
  else{const c=comps.find(c=>c.mem.includes(sel));h+=`<h2>Why stranded?</h2><p class="muted">${ns.length?`Trapped in an island of ${c.mem.length} words — none can reach POOP.`:"No word is one letter away from this one."}</p>`}
  h+=`<h2>One-letter neighbours</h2><div class="chips">${ns.length?ns.slice().sort((a,b)=>(dist[a]<0?99:dist[a])-(dist[b]<0?99:dist[b])).map(chip).join(""):'<span class="muted">none</span>'}</div>`;
  b.innerHTML=h;b.querySelectorAll("[data-w]").forEach(e=>e.onclick=()=>goWord(e.dataset.w));const f=$("frame");if(f)f.onclick=()=>frame()}
function select(i,hash=true){sel=i;onPath=i>=0&&dist[i]>=0?dag(i):new Set();nbs=new Set(i>=0?neighbors[i]:[]);route=i>=0?(ladders(i,1)[0]||[]):[];
  if(hash)history.replaceState(null,"",i>=0?"#"+words[i]:location.pathname+location.search);details();sched()}
function frame(){if(!route.length)return;const b={x0:1e9,y0:1e9,x1:-1e9,y1:-1e9};route.forEach(i=>{b.x0=Math.min(b.x0,X[i]);b.x1=Math.max(b.x1,X[i]);b.y0=Math.min(b.y0,Y[i]);b.y1=Math.max(b.y1,Y[i])});fly(fit(b,1.5))}
function goWord(w){const i=idx.get(String(w||"").trim().toLowerCase()),inp=$("search");if(i===undefined){inp.setCustomValidity("Not in this word list");inp.reportValidity();return}inp.setCustomValidity("");select(i);fly({s:Math.max(s,1.7),x:X[i],y:Y[i]})}
// ---------- input ----------
function pick(cx,cy){const wx=(cx-px)/s,wy=(cy-py)/s,th=Math.max(10,9/s);let b=-1,bd=1e9;
  for(let i=0;i<n;i++){let d=Math.hypot(X[i]-wx,Y[i]-wy);if(s>=.5&&MODE[i]!==2){const k=MODE[i]===0?(LF[i]?-1:1):1,o=MODE[i]===0?[Math.cos(LR[i]),Math.sin(LR[i])]:[1,0];const L=9+14.5;d=Math.min(d,Math.hypot(X[i]+o[0]*k*L-wx,Y[i]+o[1]*k*L-wy)-8)}if(d<th&&d<bd){b=i;bd=d}}return b}
const ptr=new Map();let moved=0,pinch=0;const pd=()=>{const[a,b]=[...ptr.values()];return Math.hypot(a.x-b.x,a.y-b.y)};
function zoomAt(x,y,ns){ns=clampS(ns);px=x-(x-px)*ns/s;py=y-(y-py)*ns/s;s=ns;sched()}
cv.addEventListener("pointerdown",e=>{cv.setPointerCapture(e.pointerId);ptr.set(e.pointerId,{x:e.clientX,y:e.clientY});moved=0;cancelAnimationFrame(anim);if(ptr.size===2)pinch=pd();cv.classList.add("drag");$("tip").style.display="none"});
cv.addEventListener("pointermove",e=>{const r=cv.getBoundingClientRect(),x=e.clientX-r.left,y=e.clientY-r.top;
  if(ptr.has(e.pointerId)){const p=ptr.get(e.pointerId),dx=e.clientX-p.x,dy=e.clientY-p.y;p.x=e.clientX;p.y=e.clientY;moved+=Math.abs(dx)+Math.abs(dy);
    if(ptr.size===1){px+=dx;py+=dy;sched()}else if(ptr.size===2){const d=pd();zoomAt(x,y,s*d/pinch);pinch=d}return}
  const h=pick(x,y);if(h!==hov){hov=h;sched()}const t=$("tip");if(h>=0){t.style.display="block";t.style.left=Math.min(x+16,W-150)+"px";t.style.top=(y+16)+"px";t.innerHTML=`<span style="color:${COL[h]}">${words[h]}</span><small>${dist[h]<0?"can't reach POOP":dist[h]===0?"the target":dist[h]+" moves to POOP"}</small>`}else t.style.display="none"});
cv.addEventListener("pointerup",e=>{const r=cv.getBoundingClientRect();if(ptr.size===1&&moved<5){const h=pick(e.clientX-r.left,e.clientY-r.top);select(h>=0&&h!==T?h:-1)}ptr.delete(e.pointerId);cv.classList.remove("drag")});
cv.addEventListener("pointercancel",e=>{ptr.delete(e.pointerId);cv.classList.remove("drag")});
cv.addEventListener("pointerleave",()=>{if(hov>=0){hov=-1;sched()}$("tip").style.display="none"});
cv.addEventListener("wheel",e=>{e.preventDefault();cancelAnimationFrame(anim);const r=cv.getBoundingClientRect();zoomAt(e.clientX-r.left,e.clientY-r.top,s*Math.exp(-e.deltaY*(e.ctrlKey?.01:.0016)))},{passive:false});
addEventListener("keydown",e=>{if(e.key==="Escape")select(-1);if(e.key==="/"&&!/INPUT/.test(document.activeElement.tagName)){e.preventDefault();$("search").focus()}});
addEventListener("hashchange",()=>{const w=decodeURIComponent(location.hash.slice(1)).toLowerCase();if(idx.has(w))goWord(w)});addEventListener("resize",()=>resize(false));
// ---------- sidebar ----------
$("total").textContent=n.toLocaleString();$("reach").textContent=reach.length.toLocaleString();$("stuck").textContent=(n-reach.length).toLocaleString();$("maxd").textContent=maxD;
$("bar").style.background="linear-gradient(90deg,"+Array.from({length:12},(_,k)=>ramp(k/11)).join(",")+")";
const fr=document.createDocumentFragment();words.forEach(w=>{const o=document.createElement("option");o.value=w;fr.appendChild(o)});$("wl").appendChild(fr);
$("go").onclick=()=>goWord($("search").value);$("search").addEventListener("keydown",e=>{if(e.key==="Enter")goWord($("search").value)});
$("all").onchange=e=>{showAll=e.target.checked;sched()};
$("home").onclick=()=>{select(-1);fly(fit(mainBox,1.04))};$("cut").onclick=()=>fly(fit({x0:zone.x0-60,y0:zone.y0-100,x1:zone.x1+60,y1:zone.y1+60},1.05));
$("rand").onclick=()=>{const c=reach.filter(i=>dist[i]>=3);goWord(words[c[Math.floor(Math.random()*c.length)]])};
$("hardest").innerHTML=reach.slice().sort((a,b)=>dist[b]-dist[a]||(words[a]<words[b]?-1:1)).slice(0,8).map(i=>`<button data-w="${words[i]}" style="color:${COL[i]}">${words[i]}<small>${dist[i]}</small></button>`).join("");
$("strand").innerHTML=iso.slice(0,10).map(chip).join("");
document.querySelectorAll("#intro [data-w]").forEach(b=>b.onclick=()=>goWord(b.dataset.w));
resize(true);select(-1,false);const h0=decodeURIComponent(location.hash.slice(1)).toLowerCase();if(idx.has(h0))goWord(h0);
if(document.fonts&&document.fonts.load)document.fonts.load(`700 12px ${MONO}`).then(sched).catch(()=>{});
})();
