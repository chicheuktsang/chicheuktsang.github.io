#
# dilatations.py
#

# Goal - compute (normalised) dilatations of (triangulation, fibre) pairs

import regina
import snappy

from snappy import Manifold

from sage.arith.functions import lcm
from sage.arith.misc import divisors, factor, gcd
from sage.numerical.mip import MIPSolverException, MixedIntegerLinearProgram
from sage.geometry.polyhedron.constructor import Polyhedron
from sage.matrix.constructor import Matrix
from sage.modules.free_module_integer import IntegerLattice
from sage.modules.free_module_element import vector
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.rings.real_mpfr import RR
from sage.rings.qqbar import QQbar
from sage.geometry.cone import Cone
from sage.functions.log import log
from sage.calculus.var import var
from sage.calculus.functional import derivative
from sage.symbolic.relation import solve
from sage.symbolic.expression_conversions import polynomial, laurent_polynomial

from veering.sage_tools import matrix_laurent_to_poly, normalise_poly
from veering.file_io import parse_data_file, write_data_file
from veering.taut import liberal, isosig_to_tri_angle
from veering.taut_polynomial import taut_polynomial_via_tree, taut_polynomial_via_fox_calculus
from veering.taut_polytope import min_neg_euler_carried, projection_to_homology, taut_rays_matrix, taut_rays
from veering.taut import liberal
from veering.transverse_taut import is_transverse_taut
from veering.taut_homology import edge_equation_matrix_taut, elem_vector, faces_in_smith, rank_of_quotient, group_ring, faces_in_laurent, epimorphism_in_laurent
from veering.fundamental_domain import non_tree_face_cycles
from veering.fundamental_group import fundamental_group

@liberal
def dilatation_betti_one_fibred(tri, angle):
    delta = alex_polynomial_via_fox_calculus(tri, angle)
    theta = taut_polynomial_via_fox_calculus(tri, angle)
    delta_span = max(i[0] for i in delta.exponents()) - min(i[0] for i in delta.exponents())
    euler = delta_span - 1
    R = theta.parent()
    a = R('a')
    theta = theta.polynomial(a)
    dil = max(theta.real_roots())
    return dil**euler, euler


def dilatation_script_betti_one(report = 100, start = 0, end = 87047, filename = "betti_one_dilatations.txt"):
    data = parse_data_file("veering_census_with_data.txt")
    data = data[start:end]
    out_filename = filename
    out = [] 
    for i, line in enumerate(data): 
        line = line.split(" ") 
        sig = line[0]
        if i % report == 0:
            print(i, sig, len(out))
        if line[1] == "F0":  # fibered
            tri, angle = isosig_to_tri_angle(sig) 
            if tri.homology().rank() == 1:  # b_1 = 1
                dil, euler = dilatation_betti_one_fibred(tri, angle)
                out.append( [str(i+start), sig, str(dil), str(euler)] ) 
        if i % (10*report) == 0 and len(out) > 0: 
            write_data_file(out, out_filename)
    write_data_file(out, out_filename)


@liberal
def rays_in_homology(tri, angle):
    rays = taut_rays(tri, angle)
    if len(rays) == 0:
        return []
    else:
        A = projection_to_homology(tri, angle)
        projectedRays = [A*v for v in rays]
        C = Cone(projectedRays)
        rays = C.rays()
        M = rays.matrix()
    return M


@liberal
def alex_polynomial_via_fox_calculus(tri, angle, simplified = True):
    ZH = group_ring(tri, angle, [], alpha = True)
    P = ZH.polynomial_ring() 
    fl = faces_in_laurent(tri, angle, [], ZH)  # images in ZZ[H_1/torsion]
    flt = fl
    G = fundamental_group(tri, angle, simplified = False)
    if simplified:
        G = G.simplified()
        indices = [int(str(x)[1:]) for x in G.gens()]  # the hackest of hacks
        flt = [flt[i] for i in indices]
    M = G.alexander_matrix(flt)
    N = matrix_laurent_to_poly(M, ZH, P)
    n = len(G.gens()) - 1
    poly = gcd(N.minors(n))
    return normalise_poly(poly, ZH, P)


def rough_PF_part(p):
    var('X,Y')
    P = factor(p)
    list = [X**2+1,X**4-X**2+1,-X**4+Y]
    list = [polynomial(s,base_ring=QQ) for s in list]
    f = 1
    for q in P:
        r = q[0]
        if r(1,Y)!=0 and r(X,1)!=0 and r not in list:
            f = f*q[0]
    return f


def naive_eq_solver(symb1,symb2):
    var('X,Y')
    allsoln = solve([symb1==0,symb2==0],X,Y,solution_dict=True)
    soln = []
    for s in allsoln:
        keys = s.keys()
        if X in keys and Y in keys:
            if s[X].is_real() == True and s[Y].is_real() == True:
                soln.append([s[X].n(), s[Y].n()])
    return soln


@liberal    
def dilatation_betti_two_fibred(tri, angle):
    delta = alex_polynomial_via_fox_calculus(tri, angle)
    theta = taut_polynomial_via_fox_calculus(tri, angle)
    R = rays_in_homology(tri, angle)
    alexexp = delta.exponents()
    v0 = R.row(0)
    eval0 = [v0[0]*w[0]+v0[1]*w[1] for w in alexexp]
    N0 = max(eval0)-min(eval0) 
    v1 = R.row(1)
    eval1 = [v1[0]*w[0]+v1[1]*w[1] for w in alexexp]
    N1 = max(eval1)-min(eval1)
    N = lcm(N0,N1)
    var('X,Y')
    theta = theta(X**(R[0,0]*N/N0)*Y**(-R[0,0]*N/N0+R[1,0]*N/N1),X**(R[0,1]*N/N0)*Y**(-R[0,1]*N/N0+R[1,1]*N/N1))
    thetapoly = laurent_polynomial(theta, base_ring=QQ)
    thetapoly = rough_PF_part(thetapoly)
    theta=(thetapoly*X)/X
    theta=theta.full_simplify()
    PX = min(i[0] for i in thetapoly.exponents())
    PY = min(i[1] for i in thetapoly.exponents())
    P = (max(i[1] for i in thetapoly.exponents())+min(i[1] for i in thetapoly.exponents()))/2
    P = QQ(P)
    thetaY = derivative(theta,Y)
    q = P*theta - Y*thetaY
    q = q.full_simplify()
    if thetaY(Y**2,Y) == 0 or q(Y**2,Y) == 0:
        thetapoly = thetapoly*X**(-PX)*Y**(-PY)
        thetapoly = thetapoly(Y**2,Y)
        thetapoly = polynomial(thetapoly, base_ring=QQbar)
        dil = max(thetapoly.real_roots())
        return dil**(2*N), N, 0
    else:
        theta = theta*X**(-PX)*Y**(-PY)
        theta = theta.full_simplify()
        thetapoly = polynomial(theta, base_ring=QQbar)
        var('x,y')
        GX = gcd([i[0] for i in thetapoly.exponents()])
        GY = gcd([i[1] for i in thetapoly.exponents()])
        thetagcd = theta(x**(1/GX),y**(1/GY))
        thetagcd = thetagcd(X,Y)
        thetagcdpoly = polynomial(thetagcd, base_ring=QQbar)
        thetagcdY = derivative(thetagcd,Y)
        thetagcdYpoly = polynomial(thetagcdY, base_ring=QQbar)
        qpoly = laurent_polynomial(q, base_ring=QQ)
        qPX = min(i[0] for i in qpoly.exponents())
        qPY = min(i[1] for i in qpoly.exponents())
        q = q*X**(-qPX)*Y**(-qPY)
        qgcd = q(x**(1/GX),y**(1/GY))
        qgcd = qgcd(X,Y)
        qgcdpoly = polynomial(qgcd, base_ring=QQbar)
        solngcd = naive_eq_solver(thetagcd,qgcd)
        for s in solngcd:
            if s[0]**(1/GX) > 1 and s[1]**(1/GY) > 1 and s[1]**(1/GY) < s[0]**(1/GX):
                return s[0]**(N/GX), N, 0
        return 1, N, 1


def dilatation_script_one_cusp_betti_two(report = 100, start = 0, end = 87047, filename="one_cusp_betti_two_dilatations.txt"):
    data = parse_data_file("veering_census_with_data.txt")
    data = data[start:end]
    out_filename = filename
    out = [] 
    failcount = 0
    for i, line in enumerate(data): 
        line = line.split(" ") 
        sig = line[0]
        if i % report == 0:
            print(i, sig, len(out))
        if line[1] == "F0" and line[2] == "1":  # fibered
            tri, angle = isosig_to_tri_angle(sig) 
            if tri.homology().rank() == 2:  # b_1 = 2
                out.append([str(i+start), sig])
                if len(out) > 0: 
                    write_data_file(out, out_filename)
                dil, euler, fail = dilatation_betti_two_fibred(tri, angle)
                if fail == 0:
                    fail = ''
                if fail == 1:
                    failcount = failcount+1
                    fail = 'failed'
                out[-1]=[str(i+start), sig, str(dil), str(euler), fail] 
                if len(out) > 0: 
                    write_data_file(out, out_filename)
    out.append([str(failcount), 'fails'])
    write_data_file(out, out_filename)


def eucl_eq_solver(poly1,poly2,orig):
    var('X,Y')
    if str(poly2.parent()) == 'Multivariate Polynomial Ring in X, Y over Algebraic Field':
        eY1=[i[1] for i in poly1.exponents()]; max(eY1)
        eY2=[i[1] for i in poly2.exponents()]; max(eY2)
        r=poly2.coefficient({Y:max(eY2)})*poly1-poly1.coefficient({Y:max(eY1)})*Y**(max(eY1)-max(eY2))*poly2
        r=r.full_simplify()
        r=polynomial(r,base_ring=QQbar)
        poly1=poly2
        poly2=r      
        return eucl_eq_solver(poly1,poly2,orig)
    else:
        sXlist=poly2.real_roots()
        soln = []
        for sX in sXlist:
            if sX > 1:
                f=orig(sX,Y)
                f=polynomial(f,base_ring=RR)
                sYlist=f.real_roots()
                for sY in sYlist:
                    soln.append([sX,sY])
        return soln


@liberal
def dilatation_betti_two_fibred_eucl(tri, angle):
    delta = alex_polynomial_via_fox_calculus(tri, angle)
    theta = taut_polynomial_via_fox_calculus(tri, angle)
    R = rays_in_homology(tri, angle)
    alexexp = delta.exponents()
    v0 = R.row(0)
    eval0 = [v0[0]*w[0]+v0[1]*w[1] for w in alexexp]
    N0 = max(eval0)-min(eval0) 
    v1 = R.row(1)
    eval1 = [v1[0]*w[0]+v1[1]*w[1] for w in alexexp]
    N1 = max(eval1)-min(eval1)
    N = lcm(N0,N1)
    var('X,Y')
    theta = theta(X**(R[0,0]*N/N0)*Y**(-R[0,0]*N/N0+R[1,0]*N/N1),X**(R[0,1]*N/N0)*Y**(-R[0,1]*N/N0+R[1,1]*N/N1))
    thetapoly = laurent_polynomial(theta, base_ring=QQ)
    thetapoly = rough_PF_part(thetapoly)
    theta=(thetapoly*X)/X
    theta=theta.full_simplify()    
    PX = min(i[0] for i in thetapoly.exponents())
    PY = min(i[1] for i in thetapoly.exponents())
    P = (max(i[1] for i in thetapoly.exponents())+min(i[1] for i in thetapoly.exponents()))/2
    P = QQ(P)
    thetaY = derivative(theta,Y)
    q = P*theta - Y*thetaY
    q = q.full_simplify()
    if thetaY(Y**2,Y) == 0 or q(Y**2,Y) == 0:
        thetapoly = thetapoly*X**(-PX)*Y**(-PY)
        thetapoly = thetapoly(Y**2,Y)
        thetapoly = polynomial(thetapoly, base_ring=QQbar)
        dil = max(thetapoly.real_roots())
        return dil**(2*N), N, 0
    else:
        theta = theta*X**(-PX)*Y**(-PY)
        thetapoly = polynomial(theta, base_ring=QQbar)
        qpoly = laurent_polynomial(q, base_ring=QQ)
        qPX = min(i[0] for i in qpoly.exponents())
        qPY = min(i[1] for i in qpoly.exponents())
        q = q*X**(-qPX)*Y**(-qPY)
        qpoly = polynomial(q, base_ring=QQbar)
        soln = eucl_eq_solver(thetapoly,qpoly,qpoly)
        cand = 1
        for s in soln:
            if s[0] > 1 and s[1] > 1 and s[1] < s[0]:
                if cand == 1:
                    cand=s[0]
                elif cand != s[0]:
                    return 1, N, 1
        if cand > 1:
            return cand**N, N, 0
        else:
            return 1, N, 1