"""Independent implementation of finite checks for the asymptotic manuscript.

Standard library only. No imports of previous project math/solver modules.
Frozen rational KKT vectors are inputs, never accepted without rechecking the
original equations and inequalities. Finite tests do not prove an asymptotic.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'verification/results/independent'


def dot(a,b): return sum(x*y for x,y in zip(a,b))
def sub(a,b): return [x-y for x,y in zip(a,b)]
def tails(v): return [sum(v[i:]) for i in range(len(v))]
def diff(v): return [v[i]-(v[i+1] if i+1<len(v) else 0) for i in range(len(v))]


def slopes(v,h,c):
    n=len(v)
    return [(h*c*sum(v)-h*sum(v[:i])-v[i])/(h*(n*c-i)) for i in range(n)]


def quadratic(v,h,c):
    n=len(v); S=1+n*h*c
    return h*h*c*c*sum(v)**2-2*h*c*S*sum((i+1)*d*t for i,(d,t) in enumerate(zip(diff(v),slopes(v,h,c))))


def matrix_by_polarization(n,h,c):
    basis=[[Q(i==j) for i in range(n)] for j in range(n)]
    diag=[quadratic(v,h,c) for v in basis]
    return [[diag[i] if i==j else (quadratic([x+y for x,y in zip(basis[i],basis[j])],h,c)-diag[i]-diag[j])/2 for j in range(n)] for i in range(n)]


def energy(v,a,t):
    n=len(v); F=n+a+t; w=tails(v)
    direct=sum(v)**2-2*F*sum((i+1)*d*(w[i]-t*v[i])/(n+a-i) for i,d in enumerate(diff(v)))
    u=diff([w[i]/(F-i) for i in range(n)])
    diag=[2*t*(i+1)*(F-i)*(F-i-1)/((n+a-i)*F)-1 for i in range(n)]
    off=[-(t-1)*(i+1)*(F-i)*(F-i-2)/((n+a-i)*F) for i in range(n-1)]
    assert direct==F*F*(sum(d*x*x for d,x in zip(diag,u))+2*sum(off[i]*u[i]*u[i+1] for i in range(n-1)))
    e0=[2*i+1-Q(2*i*(i+1),n+1) for i in range(n)]
    Hdiag=[2*(i+1)*(F-i)**2/(n+a-i) for i in range(n)]
    Hoff=[-(i+1)*(F-i)*(F-i-2)/(n+a-i) for i in range(n-1)]
    for i in range(n):
        assert diag[i]==2*i+1-Q(2*i*(i+1),1)/F+(t-1)*Hdiag[i]/F
        assert Hdiag[i]+(Hoff[i-1] if i else 0)+(Hoff[i] if i+1<n else 0)>0
    R0=sum(1/e for e in e0)
    assert direct>=sum(v)**2/R0
    return direct


def audit_energy():
    count=0
    for n in [1,2,3,6,12]:
        for h in [Q(1,20),Q(1,4),Q(1,2),Q(9,10),Q(1)]:
            for a in [Q(0),Q(1,7),Q(2)]:
                t=1/h; c=1+a/n; F=n+a+t
                positive=[Q(i+1,n*(n+1)//2) for i in range(n)]
                signed=[Q((-1)**i*(i+1),n+1) for i in range(n)]
                zero=[v-sum(signed)/n for v in signed]
                for v in [positive,signed,zero]:
                    E=energy(v,a,t)
                    if sum(v)==0:
                        assert quadratic(v,h,c)==h*h*c*E
                        if any(v):assert E>0
                    count+=1
                B=a/(n*(a+t));m=t/(a+t)
                beta=[B+m*v for v in positive]
                rhs=m*m*energy(positive,a,t)-a*a/(a+t)**2-a/n+2*F*m*B*n*(t-1)*positive[-1]/(a+1)
                assert quadratic(beta,h,c)/(h*h*c)==rhs
    for n in range(2,201):
        total=Q(0);bound=Q(0)
        for i in range(n):
            A=i+1;B=n-i;q=Q(2*A*B,n+1)
            # Reconstruct the actual diagonal weight before comparing inverses.
            # Round 30 accidentally checked q-1 instead of e0 here.
            e0=2*i+1-Q(2*i*(i+1),n+1)
            assert e0==q-1+Q(2*(i+1),n+1)
            gap=1/e0-1/q
            assert abs(gap)<=4/q**2<=2*(Q(1,A*A)+Q(1,B*B))
            total+=gap;bound+=2*(Q(1,A*A)+Q(1,B*B))
        assert abs(total)<=bound<8
    return count


def flow_matrix(n,h,c,p):
    K=[h*(n*c-i) for i in range(n)];S=1+n*h*c
    T=[[h*c-h*int(j<i)-int(j==i) for j in range(n)] for i in range(n)]
    edges={}
    M=[[h*h*c*c for _ in range(n)] for _ in range(n)]
    balance=[Q(0)]*n
    back=[-2*h*c for _ in range(n)]
    for i in range(n):
        survival=Q(1)
        for j in range(i+1,n+1):
            f=(1+i*p[i])*p[j]*survival;edges[i,j]=f
            balance[i]+=f
            lam=2*h*c*S*f/K[i];back[i]+=lam
            if j<n:balance[j]-=f;back[j]-=lam
            for k in range(n):
                M[i][k]-=lam*T[i][k]/2;M[k][i]-=lam*T[i][k]/2
                if j<n:M[j][k]+=lam*T[i][k]/2;M[k][j]+=lam*T[i][k]/2
            survival*=1-p[j]
    assert balance==[1]*n and min(back)>0
    return M,edges,back


def interpolation(points,gradients,values):
    return [[values[i]-values[j]-dot(gradients[j],sub(points[i],points[j]))-dot(sub(gradients[i],gradients[j]),sub(gradients[i],gradients[j]))/2 for j in range(len(points))] for i in range(len(points))]


def audit_flow_identity():
    count=0
    for n in [1,2,3,6]:
        for h in [Q(1,5),Q(1,2),Q(1)]:
            for c in [Q(1),Q(11,10),Q(2)]:
                S=1+n*h*c
                p=[Q(1)]+[Q(i%3+1,4) for i in range(1,n)]+[Q(1)]
                M,edges,back=flow_matrix(n,h,c,p)
                q=[Q(2,3),-Q(1,5)];z=[-Q(1,7),Q(3,11)]
                gs=[[Q(i+1,i+2),Q((-1)**i,i+3)] for i in range(n)]
                y=[x+w for x,w in zip(q,z)]
                x0=[y[k]+h*c*sum(g[k] for g in gs) for k in range(2)]
                xs=[[x0[k]-h*sum(g[k] for g in gs[:i]) for k in range(2)] for i in range(n)]
                points=xs+[y,[Q(0),Q(0)]];grads=gs+[q,[Q(0),Q(0)]]
                vals=[Q(i*i+1,i+2) for i in range(n+1)]+[Q(0)]
                slack=interpolation(points,grads,vals);star=n+1
                vs=[sub(g,q) for g in gs]
                lhs=dot(x0,x0)-S*S*dot(q,q)
                rhs=dot(z,z)+sum(M[i][j]*dot(vs[i],vs[j]) for i in range(n) for j in range(n))
                rhs+=2*h*c*sum(slack[star][i] for i in range(n))+2*slack[star][n]+2*S*slack[n][star]
                rhs+=sum(2*h*c*S*f/(h*(n*c-i))*slack[i][j] for (i,j),f in edges.items())
                rhs+=sum(back[i]*slack[n][i] for i in range(n))
                assert lhs==rhs
                count+=1
    return count


def audit_kkt(row):
    n=row['N'];h=Q(row['h']);c=Q(row['c']);r=1-h;S=1+n*h*c
    beta=list(map(Q,row['beta']));e=list(map(Q,row['e']));delta=diff(beta)
    tau=slopes(beta,h,c);phi=quadratic(beta,h,c);K=[h*(n*c-i) for i in range(n)]
    assert sum(beta)==1 and min(delta)>0 and min(e)>=0
    gaps=diff(tau)[:-1]
    assert min(gaps)>=0 and all(e[i]*gaps[i]==0 for i in range(n-1))
    assert phi==Q(row['phi'])
    M0=matrix_by_polarization(n,h,c)
    basis=[[Q(i==j) for i in range(n)] for j in range(n)]
    columns=[slopes(v,h,c) for v in basis]
    for j in range(n):
        assert dot(M0[j],beta)==phi+h*c*S*sum(e[i]*(columns[j][i]-columns[j][i+1]) for i in range(n-1))
    m=[(i+1)*delta[i]+e[i]-(e[i-1] if i else 0) for i in range(n)]
    assert min(m)>0 and sum(m)==1
    ell=[delta[i]+e[i]/(i+1) for i in range(n)]
    p=[Q(1)]+[1-e[i-1]/(i*ell[i]) for i in range(1,n)]+[Q(1)]
    assert min(p)>=0 and max(p)<=1
    Z=Q(0)
    for i in range(n):
        alpha=(1+i*p[i])/K[i]
        assert 0<r*alpha-h*(1-p[i])*Z
        Z=alpha+(1-p[i])*Z
    a=n-1
    while a and tau[a-1]==tau[a]:a-=1
    C=m[-1]/K[-1];length=n-a
    assert C==S*tau[-1]+phi/(h*c)-(n-1)*gaps[-1]
    if length>1:
        g=tau[a-1]-tau[a] if a else Q(0)
        Ds=sum((K[-1]+h*j)*r**j for j in range(length))
        Hs=h*sum((n-j)*r**(-j) for j in range(1,length))
        assert C*Ds-K[a]*a*g==(n+Hs)*beta[-1]-Hs*tau[-1]
        if n*h*h>=1 and phi>=0:
            assert Ds<(K[-1]+r)/h<=n*K[-1] and 1/S<K[-1]
            assert beta[-1]/C< K[-1]
    else:assert m[-1]==n*beta[-1]
    M,edges,back=flow_matrix(n,h,c,p)
    assert all(dot(row,beta)==phi for row in M)
    assert all(M[i][j]<0 for i in range(n) for j in range(i+1,n))
    for i in range(n):
        assert M[i][i]==phi/beta[i]+sum(-M[i][j]*beta[j]/beta[i] for j in range(n) if j!=i)
    z=[Q((-1)**i*(i+2),i+1) for i in range(n)]
    sos=sum(-M[i][j]*beta[i]*beta[j]*(z[i]/beta[i]-z[j]/beta[j])**2 for i in range(n) for j in range(i+1,n))+phi*sum(z[i]**2/beta[i] for i in range(n))
    assert sos==sum(z[i]*dot(M[i],z) for i in range(n))
    if phi>=0:assert sos>0
    return dict(N=n,h=str(h),c=str(c),phi_sign=(phi>0)-(phi<0),terminal_start=a,all_exact=True)


def audit_trials():
    rows=[]
    for n in [4,8,17,31]:
        for h in [Q(1,7),Q(2,9),Q(1,3),Q(1)]:
            t=1/h;s=2*t
            q=[Q(0)]+[sum(1/(k+s) for k in range(1,j+1)) for j in range(1,n+1)]
            v=[1/(i+s)+q[n-i]/n for i in range(n)]
            H=sum(v)
            for factor in [Q(0),Q(1,2),Q(1)]:
                a=factor/(2*t+1);c=1+a/n;B=a/(n*(a+t));m=t/(a+t)
                beta=[B+m*x/H for x in v];tau=slopes(beta,h,c)
                assert min(diff(beta))>0 and min(diff(tau)[:-1])>0
                energy(v,a,t)
                jtail=tails(v)
                J=sum((i+1)*d*(jtail[i]-t*v[i])/(n+a-i) for i,d in enumerate(diff(v)))
                J0=sum((i+1)*d*(jtail[i]-v[i])/(n-i) for i,d in enumerate(diff(v)))
                bound=(a+t-1)*sum((i+1)*d*v[i]/(n-i) for i,d in enumerate(diff(v)))
                assert abs(J-J0)<=bound
                rows.append(dict(N=n,h=str(h),a=str(a),strict_feasible=True))
    return rows


def build_and_check_counterexample(row):
    n=row['N'];h=Q(row['h']);c=Q(row['c']);S=1+n*h*c
    old=list(map(Q,row['beta']));theta=Q(1,4*n*n)
    while True:
        strict=[Q(1,n)+theta*(n-1-2*i) for i in range(n)]
        if min(diff(strict))>0 and min(diff(slopes(strict,h,c))[:-1])>0:break
        theta/=2
    mix=Q(1,4)
    while True:
        beta=[(1-mix)*x+mix*y for x,y in zip(old,strict)]
        if quadratic(beta,h,c)<0:break
        mix/=2
    tau=slopes(beta,h,c)
    assert min(diff(beta))>0 and min(diff(tau)[:-1])>0
    A=[Q(0)]*(n+1);B=[Q(0)]*(n+1);K=[h*(n*c-i) for i in range(n)]
    for i in range(n-1,-1,-1):A[i]=A[i+1]-(beta[i]-(beta[i+1] if i+1<n else 0))*tau[i]
    P=[h*c*sum(A)-h*sum(A[:i])-A[i] for i in range(n)]
    for i in range(n-1,-1,-1):B[i]=B[i+1]+(1-(A[i]-A[i+1])*P[i])/K[i]
    assert 2*S*h*c*sum(A)+h*h*c*c*sum(beta)**2==quadratic(beta,h,c)
    for i in range(n):
        dbeta=beta[i]-(beta[i+1] if i+1<n else 0)
        assert K[i]*(A[i]-A[i+1]+tau[i]*dbeta)==0
        assert K[i]*(B[i]-B[i+1])+P[i]*(A[i]-A[i+1])==1
    eps=Q(1,2)
    for attempt in range(100):
        gs=[[1+A[i]*eps**2+B[i]*eps**4,beta[i]*eps] for i in range(n)]
        x0=[1+h*c*sum(g[0] for g in gs),h*c*sum(g[1] for g in gs)]
        xs=[[x0[k]-h*sum(g[k] for g in gs[:i]) for k in range(2)] for i in range(n)]
        points=xs+[[Q(1),Q(0)],[Q(0),Q(0)]]
        gradients=gs+[[Q(1),Q(0)],[Q(0),Q(0)]]
        values=[dot(x,g)-dot(g,g)/2 for x,g in zip(points,gradients)]
        slacks=interpolation(points,gradients,values)
        margin=S*S-dot(x0,x0)
        if min(min(s) for s in slacks)>=0 and margin>0:break
        eps/=2
    else:raise AssertionError('No small perturbation found within cap')
    assert dot(x0,x0)>0
    assert all(x0[k]-h*c*sum(g[k] for g in gs)==points[n][k] for k in range(2))
    for j in range(n+2):
        scores=[dot(sub(points[i],gradients[i]),sub(gradients[j],gradients[i])) for i in range(n+2)]
        assert max(scores)==0
        assert values[j]+dot(gradients[j],gradients[j])/2==dot(points[j],gradients[j])
    for i in range(n):
        for j in range(n+2):
            assert slacks[i][j]==dot(sub(gradients[i],gradients[j]),sub(points[i],gradients[i]))
    witness=dict(N=n,h=str(h),c=str(c),epsilon=str(eps),negative_direction_Q=str(quadratic(beta,h,c)),
                 radius_margin=str(margin),points=[[str(z) for z in p] for p in points],
                 gradients=[[str(z) for z in g] for g in gradients],values=list(map(str,values)))
    path=OUT/f'counterexample_N{n}.json';path.write_text(json.dumps(witness,indent=2),encoding='utf-8')
    return dict(N=n,h=str(h),c=str(c),epsilon=str(eps),ordered_constraints=(n+2)*(n+1),
                all_constraints_exact=True,radius_margin_positive=True,file=path.relative_to(ROOT).as_posix())


def main():
    OUT.mkdir(parents=True,exist_ok=True)
    energy_count=audit_energy();flow_count=audit_flow_identity()
    source=ROOT/'verification/independent/inputs/verified.json'
    raw=json.loads(source.read_text(encoding='utf-8'))
    kkt=[audit_kkt(row) for row in raw['kkt_cases']]
    trials=audit_trials()
    witnesses=[build_and_check_counterexample(row) for row in raw['kkt_cases'] if Q(row['phi'])<0]
    result=dict(implementation='standard-library-only; no prior project math imports',
                audit_revision='round31: actual e0 reciprocal comparison, with signed difference',
                energy_vector_cases=energy_count,arbitrary_data_flow_identities=flow_count,
                harmonic_sum_bounds=list(range(2,201)),kkt_cases=kkt,trial_cases=trials,counterexamples=witnesses,
                frozen_input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),all_checks=True,
                scope='Exact finite checks and original-coordinate witnesses. General proofs and uniform limits are in the manuscript.')
    (OUT/'verification.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps(dict(energy_vector_cases=energy_count,arbitrary_flow_identities=flow_count,kkt_cases=len(kkt),
                         positive_phi_SOS_cases=sum(row['phi_sign']>=0 for row in kkt),trial_cases=len(trials),
                         counterexamples=witnesses,all_checks=True),indent=2))


if __name__=='__main__':main()
