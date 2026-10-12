#!/usr/bin/env python3
"""Independent checks of Sections 3, 7--10 of the uploaded proof.

Finite exact tests are regression checks, not proofs for arbitrary N.
Large-N values are numerical diagnostics, not asymptotic certification.
"""
from fractions import Fraction as R
import json
import math
from pathlib import Path


def tails(p):
    w = [R(0)] * len(p)
    acc = R(0)
    for i in range(len(p)-1, -1, -1):
        acc += p[i]
        w[i] = acc
    return w


def direct_energy(p, a, t):
    n = len(p)
    w = tails(p)
    total = sum(p)
    f = n+a+t
    return total*total-2*f*sum((i+1)*(p[i]-(p[i+1] if i+1<n else 0))*(w[i]-t*p[i])/(n+a-i) for i in range(n))


def tridiagonal_energy(p, a, t):
    n = len(p)
    f = n+a+t
    w = tails(p)
    z = [w[i]/(f-i) for i in range(n)] + [R(0)]
    u = [z[i]-z[i+1] for i in range(n)]
    diagonals = [2*t*(i+1)*(f-i)*(f-i-1)/((n+a-i)*f)-1 for i in range(n)]
    edges = [-(t-1)*(i+1)*(f-i)*(f-i-2)/((n+a-i)*f) for i in range(n-1)]
    q = sum(diagonals[i]*u[i]**2 for i in range(n))
    q += 2*sum(edges[i]*u[i]*u[i+1] for i in range(n-1))
    return f*f*q


def original_q(beta, a, t):
    n = len(beta)
    h = 1/t
    c = 1+a/n
    ss = 1+n*h*c
    rows = []
    for i in range(n):
        tv = h*c*sum(beta)-h*sum(beta[:i])-beta[i]
        rows.append(tv/(h*(n+a-i)))
    return h*h*c*c-2*h*c*ss*sum((i+1)*(beta[i]-(beta[i+1] if i+1<n else 0))*rows[i] for i in range(n))


def direction(n, t):
    s = 2*t
    q = [R(0)]
    for j in range(1, n+1):
        q.append(q[-1]+1/(j+s))
    return [1/(i+s)+q[n-i]/n for i in range(n)], q


def exact_checks():
    counts = dict(energy_identity=0, matrix_decomposition=0, shifted_objective=0,
                  slater_direction=0, u_formula=0, resolvent_absolute_bound=0,
                  corrected_energy_weight_bound=0, perturbation_bound=0)
    for n in range(1, 11):
        for t in [R(1), R(5,4), R(2), R(4), R(20)]:
            for a in [R(0), R(1,13), R(1,3), R(2)]:
                f = n+a+t
                for mode in range(3):
                    p = [R(((7*i+3*mode)%11)-5, i+1) for i in range(n)]
                    if mode==1:
                        p[-1] -= sum(p)
                    elif mode==2:
                        p[-1] += 1-sum(p)
                    assert direct_energy(p,a,t)==tridiagonal_energy(p,a,t)
                    counts['energy_identity'] += 1
                for i in range(n):
                    d = n+a-i
                    zz = f-i
                    ee = 2*t*(i+1)*zz*(zz-1)/(d*f)-1
                    base = 2*i+1-2*R(i*(i+1),1)/f
                    hh = 2*(i+1)*zz*zz/d
                    assert ee==base+(t-1)*hh/f
                    counts['matrix_decomposition'] += 1
                p = [R(i+1,n*(n+1)//2) for i in range(n)]
                b = a/(n*(a+t))
                m = t/(a+t)
                beta = [b+m*x for x in p]
                lhs = original_q(beta,a,t)/((1/t)**2*(1+a/n))
                rhs = m*m*direct_energy(p,a,t)-a*a/(a+t)**2-a/n+2*f*m*b*n*(t-1)*p[-1]/(a+1)
                assert lhs==rhs
                counts['shifted_objective'] += 1
            v,q = direction(n,t)
            for a in [R(0), R(1,2)/(2*t+1), 1/(2*t+1)]:
                b = a/(n*(a+t))
                m = t/(a+t)
                beta = [b+m*x/sum(v) for x in v]
                assert sum(beta)==1
                assert all(beta[i]>(beta[i+1] if i+1<n else 0) for i in range(n))
                slopes = [(a/n+sum(beta[i:])-t*beta[i])/(n+a-i) for i in range(n)]
                assert all(slopes[i]>slopes[i+1] for i in range(n-1))
                counts['slater_direction'] += 1
                w=tails(v)
                gamma=[(i+1)*(v[i]-(v[i+1] if i+1<n else 0)) for i in range(n)]
                ja=sum(gamma[i]*(w[i]-t*v[i])/(n+a-i) for i in range(n))
                j0=sum(gamma[i]*(w[i]-v[i])/(n-i) for i in range(n))
                assert abs(ja-j0)<=(a+t-1)*sum(gamma[i]*v[i]/(n-i) for i in range(n))
                counts['perturbation_bound'] += 1
            w=tails(v)
            z=[w[i]/(n+1-i) for i in range(n)]+[R(0)]
            for i in range(n):
                j=n-i
                ll=sum(1/(k+2*t) for k in range(i,n))
                expected=((j+1)/(i+2*t)-ll+(j-2*t*q[j])/n)/(j*(j+1))
                assert z[i]-z[i+1]==expected
                counts['u_formula']+=1
                e0=2*i+1-R(2*i*(i+1),n+1)
                assert e0<=3*(i+2*t)*j/n
                counts['corrected_energy_weight_bound']+=1
    for n in range(2,101):
        for i in range(n):
            aa=i+1
            bb=n-i
            qq=R(2*aa*bb,n+1)
            ee=2*i+1-R(2*i*(i+1),n+1)
            assert ee==qq-1+R(2*(i+1),n+1)
            assert abs(1/ee-1/qq)<=4/qq**2<=2*(R(1,aa*aa)+R(1,bb*bb))
            counts['resolvent_absolute_bound']+=1
    return counts


def numerical_checks():
    import numpy as np
    rows=[]
    for n in [100,1000,10000,100000,1000000]:
        ii=np.arange(n,dtype=np.float64)
        jj=n-ii
        e0=2*ii+1-2*ii*(ii+1)/(n+1)
        rn=float(np.sum(1/e0))
        harmonic=float(np.sum(1/np.arange(1,n+1,dtype=np.float64)))
        for t in [1.0,2.0,20.0]:
            ss=2*t
            qq=np.concatenate(([0.0],np.cumsum(1/(np.arange(1,n+1,dtype=np.float64)+ss))))
            vv=1/(ii+ss)+qq[n-np.arange(n)]/n
            hn=float(np.sum(vv))
            ww=np.cumsum(vv[::-1])[::-1]
            zz=ww/(jj+1)
            uu=zz-np.concatenate((zz[1:],[0.0]))
            q1=float((n+1)**2*np.sum(e0*uu*uu))
            gamma=(ii+1)*(vv-np.concatenate((vv[1:],[0.0])))
            bounded=float(n*np.sum(gamma*vv/jj))
            energies=[]
            for a in [0.0,1/(2*t+1)]:
                ff=n+a+t
                jjvalue=float(np.sum(gamma*(ww-t*vv)/(jj+a)))
                energy=(hn*hn-2*ff*jjvalue)/(hn*hn)
                energies.append(dict(a=a, energy_times_log_n=energy*math.log(n)))
            rows.append(dict(n=n,t=t,rn_minus_harmonic=rn-harmonic,
                             hn_minus_2_log_n=hn-2*math.log(n),
                             q1_over_4_log_n=q1/(4*math.log(n)),
                             n_gamma_v_over_j=bounded, energies=energies))
    return rows


def main():
    result={
        'scope':'Independent finite exact algebra checks and floating point diagnostics; these do not certify infinite parameter statements.',
        'corrected_errors':[
            'e_i^0 = q_i - 1 + 2(i+1)/(N+1), not q_i - 1. The reciprocal comparison needs absolute values.',
            'e_i^0 <= 2(i+s)j/N is false in general. The factor 3 is valid for s >= 2.'
        ],
        'exact_counts':exact_checks(),
        'numeric_rows':numerical_checks(),
    }
    out=Path(__file__).with_name('check_asymptotic_results.json')
    out.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'output':str(out),'exact_counts':result['exact_counts'],'large_n_examples':result['numeric_rows'][-3:]},indent=2,ensure_ascii=False))


if __name__=='__main__':
    main()
