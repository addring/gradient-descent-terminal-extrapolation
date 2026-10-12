"""Independent exact audit of Sections 2, 4, 5, 6 of the supplied proof.

Uses only the Python standard library. Explicit active-set candidates were
located during an exploratory numerical phase. This reproducible audit solves
the original KKT equations afresh using Fraction arithmetic and checks every
constraint, sign, complementarity equation, and reported identity exactly.
Neither a numerical solver nor prior project code/data is used in this file.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import random


KKT_CANDIDATES = [
    (4, F(1,2), F(1), []),
    (4, F(1,2), F(21,20), []),
    (4, F(1,2), F(11,10), [2]),
    (5, F(1,2), F(21,20), []),
    (9, F(1,3), F(1), []),
    (9, F(1,3), F(101,100), [7]),
    (9, F(1,3), F(21,20), [6,7]),
    (16, F(1,4), F(101,100), [0,13,14]),
    (3, F(2,3), F(21,20), []),
    (6, F(3,4), F(21,20), []),
    (10, F(4,5), F(51,50), []),
    (12, F(4,5), F(51,50), []),
]
ACTIVE_SETS = {(n,h,c): active for n,h,c,active in KKT_CANDIDATES}


def zeros(n, m):
    return [[F(0) for _ in range(m)] for _ in range(n)]


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), F(0))


def mv(a, b):
    return [dot(row, b) for row in a]


def transpose(a):
    return [list(x) for x in zip(*a)]


def matmul(a, b):
    bt = transpose(b)
    return [[dot(row, col) for col in bt] for row in a]


def solve(a, b):
    n = len(a)
    c = [list(row)+[rhs] for row, rhs in zip(a, b)]
    for k in range(n):
        pivot = next(i for i in range(k, n) if c[i][k])
        c[k], c[pivot] = c[pivot], c[k]
        v = c[k][k]
        c[k] = [x/v for x in c[k]]
        for i in range(n):
            if i != k and c[i][k]:
                v = c[i][k]
                c[i] = [x-v*y for x, y in zip(c[i], c[k])]
    return [row[-1] for row in c]


def build(n, h, c):
    S = 1+n*h*c
    K = [h*(n*c-i) for i in range(n)]
    T = [[h*c-h*(j<i)-F(i == j) for j in range(n)] for i in range(n)]
    D = [[F(i == j)-F(j == i+1) for j in range(n)] for i in range(n)]
    A = [[T[i][j]/K[i]-T[i+1][j]/K[i+1] for j in range(n)] for i in range(n-1)]
    # Recover the objective matrix by polarization of the defining scalar Q.
    def q(x):
        delta = mv(D, x)
        tau = [v/k for v, k in zip(mv(T, x), K)]
        return h*h*c*c*sum(x)**2-2*h*c*S*sum((i+1)*delta[i]*tau[i] for i in range(n))
    basis = [[F(i == j) for j in range(n)] for i in range(n)]
    M = zeros(n, n)
    for i in range(n):
        M[i][i] = q(basis[i])
    for i in range(n):
        for j in range(i+1, n):
            M[i][j] = M[j][i] = (q([x+y for x, y in zip(basis[i], basis[j])])-M[i][i]-M[j][j])/2
    return S, K, T, D, A, M


def exact_kkt(n, h, c, active=None):
    S, K, T, D, A, M = build(n, h, c)
    if active is None:
        active = ACTIVE_SETS[(n,h,c)]
    size = n+1+len(active)
    mat = zeros(size, size)
    rhs = [F(0)]*size
    rhs[n] = F(1)
    for i in range(n):
        mat[i][:n] = M[i][:]
        mat[i][n] = F(-1)
        for j, k in enumerate(active):
            mat[i][n+1+j] = -h*c*S*A[k][i]
        mat[n][i] = F(1)
    for j, k in enumerate(active):
        mat[n+1+j][:n] = A[k][:]
    sol = solve(mat, rhs)
    beta = sol[:n]
    phi = sol[n]
    e = [F(0)]*n
    for j, k in enumerate(active):
        e[k] = sol[n+1+j]
    tau = [v/k for v, k in zip(mv(T,beta), K)]
    delta = mv(D,beta)
    assert min(delta) > 0
    assert all(tau[i] >= tau[i+1] for i in range(n-1))
    assert min(e) >= 0
    assert sum(beta) == 1
    assert all(e[i]*(tau[i]-tau[i+1]) == 0 for i in range(n-1))
    stationarity = mv(M,beta)
    for i in range(n):
        assert stationarity[i] == phi+h*c*S*sum(A[j][i]*e[j] for j in range(n-1))
    assert dot(beta, stationarity) == phi
    return (S, K, T, D, A, M), beta, tau, delta, e, phi, active


def audit_flow(n, h, c):
    data, beta, tau, delta, e, phi, active = exact_kkt(n,h,c)
    S,K,T,D,A,M0 = data
    r = 1-h
    offset = n*(c-1)
    B = [K[i]*(beta[i]-tau[i]) for i in range(n)]
    assert B[0] == S*beta[0]-h*c and B[0]>=F(1,n)
    assert min(B)>0
    for i in range(n-1):
        assert K[i+1]*(tau[i]-tau[i+1]) == h*B[i]/K[i]-delta[i]
        assert B[i+1] == B[i]-(K[i+1]+1)*delta[i]
        assert B[i+1] >= r*K[i+1]*B[i]/K[i]
    assert B[-1] == (1+h*offset)*beta[-1]-h*offset/n
    prev_e = [F(0)]+e[:-1]
    m = [(i+1)*delta[i]+e[i]-prev_e[i] for i in range(n)]
    w = [v/k for v,k in zip(m,K)]
    assert min(m) > 0 and sum(m) == 1
    U = [(i+1)*tau[i]-(i*tau[i-1] if i else 0) for i in range(n)]
    kappa = h*c/S-phi/(h*c*S)
    ttw = mv(transpose(T),w)
    assert all(U[i]+ttw[i] == kappa for i in range(n))
    # Every maximal slope plateau: row recurrences, endpoint bound, terminal sum.
    blocks=[]
    a=0
    while a<n:
        b=a
        while b+1<n and tau[b+1] == tau[a]: b+=1
        blocks.append([a,b])
        gap=tau[a-1]-tau[a] if a else F(0)
        assert e[b] == 0 and prev_e[a] == 0
        for i in range(a,b-1):
            assert delta[i+1] == r*delta[i]
        for i in range(a,b):
            assert w[i] == r*w[i+1]-(a*gap if i==a else 0)
        if b<n-1:
            assert m[b] >= delta[b]
            if b>a:
                assert delta[b] <= r*delta[b-1]
                assert w[b]*sum(K[i]*r**(b-i) for i in range(a,b+1))-K[a]*a*gap == sum((i+1)*delta[i] for i in range(a,b+1))
                assert m[b]/delta[b] >= K[b]*(a+b+2)/(2*K[b]+h*(b-a))
        elif phi>=0 and n*h*h>=1:
            assert m[b] > delta[b]
            if b>a:
                assert w[b] == S*tau[b]+phi/(h*c)
                length=b-a+1
                DL=sum((K[b]+h*j)*r**j for j in range(length))
                HL=h*sum((n-j)*r**(-j) for j in range(1,length))
                assert w[b]*DL-K[a]*a*gap == (n+HL)*beta[b]-HL*tau[b]
                assert beta[b]/w[b] <= (DL+HL/S)/(n+HL)
        a=b+1
    assert phi>=0 and n*h*h>=1
    ell = [delta[i]+e[i]/(i+1) for i in range(n)]
    p=[F(1)]+[1-e[i-1]/(i*ell[i]) for i in range(1,n)]+[F(1)]
    s=[1-v for v in p]
    O=[1+i*p[i] for i in range(n)]
    assert all(0<=v<=1 for v in p)
    assert all(O[i] == m[i]/ell[i] for i in range(n))
    G=[i*m[i]-prev_e[i] for i in range(n)]
    assert all(G[i] == i*(i+1)*ell[i]*p[i] for i in range(n))
    for a,b in blocks:
        gap=tau[a-1]-tau[a] if a else F(0)
        assert G[a] == a*m[a] and G[b] == (b+1)*(m[b]-delta[b])
        for i in range(a,b):
            assert G[i+1]-G[i] == (i+1)*(m[i+1]-m[i]+delta[i])
            assert m[i+1]-m[i]+delta[i] == h*(K[i]-1)*w[i+1]+delta[i]+(K[a]*a*gap if i==a else 0)
    flow=zeros(n,n+1)
    for i in range(n):
        for j in range(i+1,n+1):
            mult=F(1)
            for k in range(i+1,j): mult*=s[k]
            flow[i][j]=O[i]*p[j]*mult
    for i in range(n):
        assert sum(flow[i])-sum(flow[k][i] for k in range(i)) == 1
        assert sum(flow[i][j]*(beta[i]-(beta[j] if j<n else 0)) for j in range(i+1,n+1)) == m[i]
        for j in range(i+1,n+1):
            if flow[i][j]>0:
                # The destination may be the first node after a slope plateau.
                # Precisely the source slopes i,...,j-1 must agree.
                assert all(tau[k] == tau[i] for k in range(i,j))
    C=zeros(n,n)
    for i in range(n):
        C[i][i]=O[i]/K[i]
        for j in range(i+1,n): C[j][i]=-flow[i][j]/K[i]
    assert mv(transpose(C),beta) == w
    assert mv(C,mv(T,beta)) == U
    ct=matmul(C,T)
    M=[[h*h*c*c-h*c*S*(ct[i][j]+ct[j][i]) for j in range(n)] for i in range(n)]
    assert mv(M,beta) == [phi]*n
    alpha=[O[i]/K[i] for i in range(n)]
    Z=[F(0)]
    for i in range(n): Z.append(alpha[i]+s[i]*Z[i])
    X=[s[i]*Z[i]/alpha[i] for i in range(n)]
    assert all(0<=v<r/h for v in X)
    for i in range(n-1):
        assert X[i+1] == w[i]/w[i+1]*(1-delta[i]/ell[i])*(1+X[i])
        assert X[i+1] < r*(1+X[i])
    rho=[alpha[i]-p[i]*Z[i] for i in range(n)]
    assert all(rho[i]>=1/K[i] for i in range(n))
    for i in range(n):
        for j in range(i+1,n):
            mult=F(1)
            for k in range(i+1,j): mult*=s[k]
            bracket=h*c*rho[i]+h*(c-1)*rho[j]+p[j]*mult*(r*alpha[i]-h*s[i]*Z[i])
            assert M[i][j] == h*h*c*c-h*c*S*bracket
            assert M[i][j]<0
    tested=0
    rng=random.Random(n*99+int(h*100))
    for _ in range(7):
        z=[F(rng.randint(-10,10),rng.randint(1,7)) for _ in range(n)]
        rhs=sum(-M[i][j]*beta[i]*beta[j]*(z[i]/beta[i]-z[j]/beta[j])**2 for i in range(n) for j in range(i+1,n))
        rhs+=phi*sum(z[i]**2/beta[i] for i in range(n))
        assert dot(z,mv(M,z)) == rhs and rhs>=0
        tested+=1
    return {'N':n,'h':str(h),'c':str(c),'phi_sign':1,'phi_approx':float(phi),
            'active_slopes':active,'slope_blocks':blocks,'nonadjacent_edges':sum(flow[i][j]>0 for i in range(n) for j in range(i+2,n+1)),
            'minimum_p_approx':float(min(p)), 'minimum_beta_difference_approx':float(min(delta)),
            'exact_psd_identity_vectors':tested}


def audit_identity(n,h,c,seed):
    rng=random.Random(seed)
    S,K,T,D,A,M0=build(n,h,c)
    # Generate a nonnegative forward flow by splitting each node's incoming+1.
    flow=zeros(n,n+1)
    for i in range(n):
        out=1+sum(flow[k][i] for k in range(i))
        weights=[rng.randint(1,9) for j in range(i+1,n+1)]
        total=sum(weights)
        for j,wt in zip(range(i+1,n+1),weights): flow[i][j]=out*F(wt,total)
    def vec(): return [F(rng.randint(-8,8),rng.randint(1,8)) for _ in range(2)]
    g=[vec() for _ in range(n)]+[vec()]
    x0=vec()
    x=[]
    for i in range(n): x.append([x0[d]-h*sum(g[k][d] for k in range(i)) for d in range(2)])
    x.append([x0[d]-h*c*sum(g[k][d] for k in range(n)) for d in range(2)])
    f=[F(rng.randint(-9,9),rng.randint(1,9)) for _ in range(n+1)]
    x.append([F(0),F(0)]); g.append([F(0),F(0)]); f.append(F(0))
    star=n+1; o=n
    def Q(i,j):
        return f[i]-f[j]-dot(g[j],[a-b for a,b in zip(x[i],x[j])])-dot([a-b for a,b in zip(g[i],g[j])],[a-b for a,b in zip(g[i],g[j])])/2
    lam=[[2*h*c*S*flow[i][j]/K[i] for j in range(n+1)] for i in range(n)]
    b=[sum(lam[i])-sum(lam[k][i] for k in range(i))-2*h*c for i in range(n)]
    assert min(b)>0
    C=zeros(n,n)
    for i in range(n):
        C[i][i]=sum(flow[i])/K[i]
        for j in range(i+1,n): C[j][i]=-flow[i][j]/K[i]
    ct=matmul(C,T)
    M=[[h*h*c*c-h*c*S*(ct[i][j]+ct[j][i]) for j in range(n)] for i in range(n)]
    v=[[a-b for a,b in zip(g[i],g[o])] for i in range(n)]
    z=[a-b for a,b in zip(x[o],g[o])]
    rhs=dot(z,z)+sum(M[i][j]*dot(v[i],v[j]) for i in range(n) for j in range(n))
    rhs+=2*h*c*sum(Q(star,i) for i in range(n))+2*Q(star,o)+2*S*Q(o,star)
    rhs+=sum(lam[i][j]*Q(i,j) for i in range(n) for j in range(i+1,n+1))
    rhs+=sum(b[i]*Q(o,i) for i in range(n))
    lhs=dot(x0,x0)-S*S*dot(g[o],g[o])
    assert lhs==rhs


if __name__ == '__main__':
    identity_count=0
    for n in [1,2,3,5,8]:
        for h in [F(1,4),F(1,2),F(1)]:
            for c in [F(1),F(21,20),F(4,3)]:
                audit_identity(n,h,c,1123+identity_count)
                identity_count+=1
    print('Exact certificate identities:', identity_count, flush=True)
    flow_results=[]
    for n,h,c,_ in KKT_CANDIDATES:
        res=audit_flow(n,h,c)
        flow_results.append(res)
        print(json.dumps(res,ensure_ascii=False),flush=True)
    report={'certificate_identity_cases':identity_count,
            'flow_cases':flow_results,
            'exact_psd_identity_total':sum(x['exact_psd_identity_vectors'] for x in flow_results),
            'passed':True,
            'method':'Pure Python standard library: explicit active-set candidates; exact Fraction KKT solve and all original signs rechecked.'}
    Path(__file__).with_name('verification.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
