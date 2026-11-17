X=-1
arms={0:[[5,31,2,3],[1,31,31,3],[0,28,10,0]],1:[[4,5,28,7]],2:[[1,5,5,8],[4,6,28,X],[14,5,5,6]],
3:[[0,31,31,248],[7,0,31,12],[0,10,0,255],[48,0,1,0],[11,5,31,0]],4:[[8,28,28,1]],5:[[0,5,0,0]],
6:[[1,5,5,8],[6,5,5,X]],7:[[3,5,31,X]],8:[[3,6,31,0],[3,5,31,1],[8,31,31,1],[X,5,5,6],[11,5,31,0]],
9:[[3,5,31,0],[8,31,31,X],[11,5,31,0]],10:[[5,6,5,X]],11:[[16,6,13,X]],12:[[48,0,1,0]]}
def code(r,last):
    c=0;f=0
    for j,b in enumerate(r):
        if b==X: f|= (2 if j==0 else 1); assert j in (0,3)
        else: c|=b<<(8*j)
    return c|(f<<32)|((4 if last else 0)<<32)
def armexpr(m):
    rs=arms[m]; s=""
    for k,r in enumerate(rs[:-1]): s+=f"if k == {k} then (0x{code(r,False):X} : UInt64) else "
    return "("+s+f"(0x{code(rs[-1],True):X} : UInt64))"
def ch(ms,d):
    return "("+"".join(f"if m == {m} then {armexpr(m)} else " for m in ms)+armexpr(d)+")"
print(f"(if m < 6 then {ch(range(5),5)} else if m < 12 then {ch(range(6,11),11)} else {armexpr(12)})")
