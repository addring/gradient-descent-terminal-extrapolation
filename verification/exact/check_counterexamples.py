from fractions import Fraction as F
import json
from pathlib import Path


def dot(x,y): return sum(a*b for a,b in zip(x,y))
def sub(x,y): return tuple(a-b for a,b in zip(x,y))


def run(N,h,c):
    delta=F(1,100*N**3)
    for _ in range(100):
        beta=[F(1,N)+delta*(F(N-1,2)-i) for i in range(N)]
        K=[h*(N*c-i) for i in range(N)]
        def T(v): return [h*c*sum(v)-h*sum(v[:i])-v[i] for i in range(N)]
        tau=[z/k for z,k in zip(T(beta),K)]
        if beta[-1]>0 and all(tau[i]>tau[i+1] for i in range(N-1)):
            break
        delta/=2
    assert sum(beta)==1
    assert beta[-1]>0
    assert all(beta[i]>beta[i+1] for i in range(N-1))
    assert all(tau[i]>tau[i+1] for i in range(N-1))
    db=[beta[i]-(beta[i+1] if i+1<N else 0) for i in range(N)]
    S=1+N*h*c
    Q=h*h*c*c-2*h*c*S*sum((i+1)*db[i]*tau[i] for i in range(N))
    assert Q<0, (N,h,c,Q)
    A=[F(0)]*(N+1)
    B=[F(0)]*(N+1)
    for i in reversed(range(N)): A[i]=A[i+1]-db[i]*tau[i]
    P=T(A[:-1])
    for i in reversed(range(N)): B[i]=B[i+1]+(1-(A[i]-A[i+1])*P[i])/K[i]
    assert 2*S*h*c*sum(A[:-1])+h*h*c*c==Q
    for power in range(3,100):
        eps=F(1,2**power)
        gs=[(1+A[i]*eps**2+B[i]*eps**4,beta[i]*eps) for i in range(N)]
        x0=(1+h*c*sum(g[0] for g in gs),h*c*sum(g[1] for g in gs))
        xs=[(x0[0]-h*sum(g[0] for g in gs[:i]),x0[1]-h*sum(g[1] for g in gs[:i])) for i in range(N+1)]
        y=(x0[0]+c*(xs[-1][0]-x0[0]),x0[1]+c*(xs[-1][1]-x0[1]))
        assert y==(1,0)
        data=[(xs[i],gs[i],dot(gs[i],xs[i])-dot(gs[i],gs[i])/2) for i in range(N)]
        data.extend([((1,0),(1,0),F(1,2)),((0,0),(0,0),F(0))])
        slack={}
        for i,(xi,gi,fi) in enumerate(data):
            for j,(xj,gj,fj) in enumerate(data):
                if i==j: continue
                dij=sub(gi,gj)
                slack[i,j]=fi-fj-dot(gj,sub(xi,xj))-dot(dij,dij)/2
                assert slack[i,j]==dot(dij,sub(xi,gi))
        radius=dot(x0,x0)
        if min(slack.values())>=0 and radius<S*S: break
    else: raise RuntimeError('epsilon not found')
    assert all(slack[i,j]==0 for i in (N,N+1) for j in range(N+2) if i!=j)
    assert all(slack[i,j]>0 for i in range(N) for j in range(N+2) if i!=j)
    # Verify every affine plane lies below the active value at every gradient query.
    for xj,gj,fj in data:
        planes=[dot(sub(xi,gi),sub(gj,gi)) for xi,gi,fi in data]
        assert max(planes)==0
        assert dot(gj,xj)-dot(gj,gj)/2==fj
    return {'N':N,'h':str(h),'c':str(c),'Q_sign':'negative','epsilon':str(eps),
            'ordered_constraints':len(slack),'strict_constraints':sum(q>0 for q in slack.values()),
            'zero_constraints':sum(q==0 for q in slack.values()),
            'radius_squared_below_S_squared':True,'conjugate_planes_active_correctly':True,
            'radius_quadratic_coefficient_equals_Q':True}


if __name__=='__main__':
    cases=[(1,F(1),F(2)),(2,F(1),F(2)),(4,F(1,2),F(2)),(9,F(1,3),F(2)),
           (16,F(1,4),F(2)),(25,F(1,5),F(2)),(8,F(1),F(3,2))]
    results=[run(*case) for case in cases]
    Path(__file__).with_name('results.json').write_text(json.dumps(results,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(results,ensure_ascii=False,indent=2))
