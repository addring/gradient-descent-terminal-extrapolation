"""Targeted exact regressions and cross-implementation KKT checks.

The two corrected inequalities have general proofs in the review note.
Finite tests do not establish the asymptotic theorem.
"""
from pathlib import Path
from fractions import Fraction as Q
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'verification/results/regressions'


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    obj = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj


def main():
    old = module('project_verifier', ROOT/'verification/independent/audit_asymptotic_proof_standalone.py')
    ext = module('external_verifier', ROOT/'verification/exact/check_certificates.py')
    # Recover both bad formulas from their actual defining expressions.
    n,i = 5,4
    e=2*i+1-Q(2*i*(i+1),n+1)
    q=Q(2*(i+1)*(n-i),n+1)
    assert e != q-1 and 1/e-1/q < 0
    failure1=dict(N=n,i=i,e=str(e),q=str(q),old_rhs=str(q-1))
    n,i,s=10,9,Q(2)
    e=2*i+1-Q(2*i*(i+1),n+1)
    assert e>2*(i+s)*(n-i)/n
    failure2=dict(N=n,i=i,s=str(s),e=str(e),old_upper=str(2*(i+s)*(n-i)/n))
    inverse_cases=weight_cases=0
    signs=set()
    for n in range(2,201):
        inverse_sum=harmonic=Q(0)
        for i in range(n):
            j=n-i
            e=2*i+1-Q(2*i*(i+1),n+1)
            q=Q(2*(i+1)*j,n+1)
            rho=-1+Q(2*(i+1),n+1)
            assert e==1+Q(2*i*j,n+1)==q+rho
            assert abs(rho)<=1 and q>=Q(4,3) and e>=q/4
            gap=1/e-1/q
            signs.add((gap>0)-(gap<0))
            assert abs(gap)<=4/q**2<=2*(Q(1,(i+1)**2)+Q(1,j*j))
            inverse_sum+=1/e
            harmonic+=Q(1,i+1)
            inverse_cases+=1
            for s in [Q(2),Q(5,2),Q(4),Q(40),Q(200)]:
                assert (i+s)*j-n==i*(j-1)+(s-1)*j>=0
                assert e<=3*(i+s)*j/n
                weight_cases+=1
        assert abs(inverse_sum-harmonic)<8
    assert signs=={-1,0,1}

    # External implementation solves; the project's separately written
    # implementation recomputes Q, stationarity, all signs and the full SOS.
    cross=[]
    support_examples=[]
    for n,h,c,active in ext.KKT_CANDIDATES:
        _, beta, tau, delta, e, phi, _=ext.exact_kkt(n,h,c,active)
        row=dict(N=n,h=str(h),c=str(c),beta=list(map(str,beta)),
                 e=list(map(str,e)),phi=str(phi))
        cross.append(old.audit_kkt(row))
        ell=[delta[i]+e[i]/(i+1) for i in range(n)]
        probabilities=[Q(1)]+[1-e[i-1]/(i*ell[i]) for i in range(1,n)]+[Q(1)]
        _, edges, _=old.flow_matrix(n,h,c,probabilities)
        for (i,j),flow in edges.items():
            if flow>0:
                assert all(tau[k]==tau[i] for k in range(i,j))
                if j<n and j>i+1 and tau[j]!=tau[i]:
                    support_examples.append(dict(N=n,h=str(h),c=str(c),i=i,j=j,
                       flow=str(flow),source_slope=str(tau[i]),destination_slope=str(tau[j])))
    assert support_examples
    result=dict(passed=True,old_formula_counterexamples=[failure1,failure2],
                actual_weight_inverse_cases=inverse_cases,corrected_weight_cases=weight_cases,
                signed_inverse_differences=sorted(signs),cross_implementation_kkt_cases=cross,
                beyond_plateau_endpoint_edges=support_examples,
                scope='Finite exact regression checks; analytical proofs are in the review note.')
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'independent_regressions.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(passed=True,inverse_cases=inverse_cases,weight_cases=weight_cases,
                         cross_kkt=len(cross),support_examples=len(support_examples)),indent=2))


if __name__=='__main__':
    main()
