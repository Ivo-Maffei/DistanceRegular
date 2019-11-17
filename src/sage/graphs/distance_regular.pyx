# distutils: sources = sage/graphs/distance_regular_C/Core/DistanceRegular.c
# distutils: include_dirs = sage/graphs/distance_regular_C/

# project C import
cimport sage.graphs.distance_regular_C as c_code
cimport cython
from libc.stdlib cimport malloc, free
from cysignals.signals cimport sig_check

# python imports
from math import ceil, floor
import numpy as np

# sage imports
from sage.graphs.graph_generators import GraphGenerators
from sage.graphs.graph import Graph as Sage_Graph
from sage.arith.misc import is_prime_power, is_prime
from sage.combinat.q_analogues import q_binomial
from sage.combinat.integer_vector import IntegerVectors
from sage.modules.free_module import VectorSpace
from sage.rings.finite_rings.finite_field_constructor import GF as Sage_GF
from sage.matrix.constructor import Matrix as Sage_Matrix
from sage.rings.rational cimport Rational

# from bouwer book, we assume d \gt 3 [not sure if it works with smaller d]
def intersection_array_from_classical_parameters( const int d, const int b, const float alpha, const float beta ):
    if b == 1:
        bs = [ d *beta ] #bs will be the list {b_0, ..., b_{d-1} }
    else:
        bs = [ (b**d -1)/(b-1) * beta ]
    
    cs = [ ] # cs will be the list {c_1, ..., c_d }
    btoi = 1 # this represents b^i and it is only used if b \neq 1
    btod = b ** d # b^d used when b \neq 1
    invb = 1 #this represents 1 / b - 1 in case b \neq 1
    if b != 1 : invb = 1.0 / (b - 1.0)
    for i in range(1,d):
        if b == 1: #easy formula if b is 1
            bs.append( (d - i) * (beta - alpha * i) )
            cs.append( i * (1 + alpha * (i - 1)) )
        else :
            c = 1 + alpha * ( btoi - 1 ) * invb # 1+ \a \frac {b^{i-1} - 1}{b - 1}
            btoi = btoi * b
            c = c * (btoi - 1) * invb # c = c_i
            cs.append( c )
            bs.append( invb * (btod - btoi) * (beta - alpha * (btoi - 1) * invb) )
    # now we need to add c_d to cs
    if b == 1:
        cs.append( d * (1 + alpha * (d - 1)) )
    else :
        c = 1 + alpha * ( btoi - 1 ) * invb # 1+ \a \frac {b^{d-1} - 1}{b - 1}
        c = c * (btod - 1) * invb # c = c_d
        cs.append( c )
    return (bs + cs)

def intersection_array_from_graph( G ):
    t = G.is_distance_regular(True)
    assert t, "the graph passed is not distance_regular"
    (b,c) = t
    # annoyingly b ends with None (b_d = 0)
    # and c starts with None (c_0 = 0)
    # so trim these 2 values
    return b[:-1]+c[1:]

def halve_graph(G) :
    # we halve the graph G
    # we assume G is bipartite
    # this is  faster
    assert G.is_bipartite()
    H = GraphGenerators.EmptyGraph()
    queue = [G.vertices()[0]] # queue of vertex to follow
    H.add_vertex(G.vertices()[0])
    while queue:
        v = queue.pop(0)
        close = G.neighbors(v)
        candidate = [ x for c in close for x in G.neighbors(c) ]# flatten map G.neighbors(_) close
        for w in candidate:
            if G.distance(v,w) == 2:
                if w not in H:
                     queue.append(w)
                     H.add_vertex(w)
                H.add_edge(v,w)

    H.name("Halved %s" % G.name() )
    
    return H

def construct_halved_cube( int n ):
    def hamming_dist( str1, str2 ):
        assert len(str1) == len(str2), "Can't compute Hamming distance of 2 strings of different size!"
        counter = 0
        for i in range(0, len(str1)):
            if ( str1[i] != str2[i] ):
                counter = counter + 1
        return counter
    
    #construct the halved cube graph 1/2 Q_n ( = Q_{n-1} ^2 )
    G = GraphGenerators.CubeGraph(n-1)
    # now square the graph
    # we use the fact that the vertices are strings and their distance is their hamming_distance
    for i in G.vertices():
        for j in G.vertices():
            if hamming_dist(i, j) == 2 :
                G.add_edge(i,j)
                
    G.relabel() # label back vertices to 0,1,2,...

    G.name("Halved %d Cube"%n)
    return G

cdef bint _c_has_rank_1(v, const unsigned int nrows, const unsigned int ncols):
    assert len(v) == nrows*ncols, "wtf"
    cdef int* pxV;
    pxV = <int*> malloc(nrows*ncols*cython.sizeof(int))
    if pxV is NULL:
            raise MemoryError()
        
    for i in range(0,nrows*ncols):
            pxV[i] = v[i]
    res =  c_code.HasVectorRank1(pxV,nrows,ncols)
    free(pxV)
    return res

def _add_vectors_mod(v, w, const unsigned int q):
    return tuple(map( lambda x : sum(x) % q , zip(v,w) ))

def construct_bilinear_form_graph(const int d, const int e, const int q):

    # C code assumes the matrix is over QQ.
    # When using Z_p, this is fine as Z_p can be embedded in Q
    # and all operations done by the C-code (divmod) can be safely done
    # if instead we have F_q, q=p^n for n > 1, then the C-code works when
    # assuming that i represents g^i for some g\in F_q generator of F_q^*
    # however, in such case then we can't perform normal addition between matrices
    # since g^ì+g^j != g^(i+j)

    import time

    start = time.time()
    flattenMatrices = IntegerVectors(length=d*e,max_part=q-1)
    end = time.time()
    print("integer vectors in %.6f" % (end-start) )
    
    start = time.time()
    rank1Matrices = []
    for v in flattenMatrices:
        if Sage_Matrix(Sage_GF(q), v, nrows=d).rank() == 1:
        #if _c_has_rank_1(v, d, e):
            rank1Matrices.append(tuple(v))
    end = time.time()
    print("done calculating basis size %d in %.6f" % (len(rank1Matrices),end-start) )

    start = time.time()
    edges = []
    counter = 0
    for v in flattenMatrices:
        sig_check()
        counter += 1
        if counter % 1000 == 0:
            print("hi %d" % counter)
        for w in rank1Matrices:
                edges.append( ( tuple(v), _add_vectors_mod(v,w,q) ) )

    end = time.time()
    print("done set edges size: %d, time: %.6f" %(len(edges), end-start) )
    
    start = time.time()
    G = Sage_Graph(edges, format='list_of_edges')
    end = time.time()
    print("done constructing graph in %.6f" % (end-start) )
    
    G.name("Bilinear form graphs over F_%d with parameters (%d,%d)" %(q,d,e) )
    return G


# check if the graph G is a grassman graph
def is_Grassman( G ):
    if not G.is_distance_regular(): return False
    intArr = intersection_array_from_graph(G)
    # If G is Grassman, then we can deduce the classical paramaters from the intersection array
    (d, b, alpha, beta) = get_classical_parameters_from_intersection_array(intArr, True)

    # as an aside we don't really need to check whether b is a prime power
    # b == alpha && b != 1 && b > 0 is enough 
    return d > 2 and b == alpha and b != 1 and b > 0

def construct_extended_ternary_Golay_code_graph():

    V = VectorSpace(Sage_GF(3),12) # underlying vectorspace
    C = V.span([ (1, 0, 0, 0, 0, 0, 2, 0, 1, 2, 1, 2),
                 (0, 1, 0, 0, 0, 0, 1, 2, 2, 2, 1, 0),
                 (0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1),
                 (0, 0, 0, 1, 0, 0, 1, 1, 0, 2, 2, 2),
                 (0, 0, 0, 0, 1, 0, 2, 1, 2, 2, 0, 1),
                 (0, 0, 0, 0, 0, 1, 0, 2, 1, 2, 2, 1) ])
    # C is the codeword space
    
    G = GraphGenerators.EmptyGraph()
    G.add_vertices( map( tuple, C ) )

    generators = [ v for v in C if v.hamming_weight() == 12 ]

    for v in G:
        for s in generators:
            w = tuple( map( sum , zip(v,s) ))
            G.add_edge(v,w)
            
    G.name("Ternary Extended Golay Code Graph")
    return G

def construct_large_Witt_graph():
     # G is the generator matrix of the extended binary Goolay code
    G = np.array([ [1,0,0,0,0,0,0,0,0,0,0,0, 1,0,0,1,1,1,1,1,0,0,0,1],
                   [0,1,0,0,0,0,0,0,0,0,0,0, 0,1,0,0,1,1,1,1,1,0,1,0],
                   [0,0,1,0,0,0,0,0,0,0,0,0, 0,0,1,0,0,1,1,1,1,1,0,1],
                   [0,0,0,1,0,0,0,0,0,0,0,0, 1,0,0,1,0,0,1,1,1,1,1,0],
                   [0,0,0,0,1,0,0,0,0,0,0,0, 1,1,0,0,1,0,0,1,1,1,0,1],
                   [0,0,0,0,0,1,0,0,0,0,0,0, 1,1,1,0,0,1,0,0,1,1,1,0],
                   [0,0,0,0,0,0,1,0,0,0,0,0, 1,1,1,1,0,0,1,0,0,1,0,1],
                   [0,0,0,0,0,0,0,1,0,0,0,0, 1,1,1,1,1,0,0,1,0,0,1,0],
                   [0,0,0,0,0,0,0,0,1,0,0,0, 0,1,1,1,1,1,0,0,1,0,0,1],
                   [0,0,0,0,0,0,0,0,0,1,0,0, 0,0,1,1,1,1,1,0,0,1,1,0],
                   [0,0,0,0,0,0,0,0,0,0,1,0, 0,1,0,1,0,1,0,1,0,1,1,1],
                   [0,0,0,0,0,0,0,0,0,0,0,1, 1,0,1,0,1,0,1,0,1,0,1,1] ])
    
    # condtruction is here: http://mathworld.wolfram.com/LargeWittGraph.html
    def codeword_weight( codeword ):
        cdef int weight = 0
        for i in codeword:
            if i == 1: weight += 1

        return weight

    def orthogonal( vec1, vec2 ):
        for (i,j) in zip(vec1,vec2):
            if i*j != 0:
                return False
        return True
    
    vertices=[]
    # we will add tuples as vertices via add_vertex(tuple([1,0,1....]))
    cdef int vertices_found = 0 #max is 759
    for vec in IntegerVectors(k=12,max_part=1): #iterate over all binary vectors of size 12
        codeword = np.matmul(vec,G) % 2
        if (codeword_weight(codeword) == 8 ): # is a valid vertex
            vertices.append(tuple(codeword))
            vertices_found += 1
            if vertices_found == 759: break

    edges = []
    # here W contains all 759 vertices
    for v in vertices:
        for w in vertices:
            # check if w,v are orthogonal and if so, add edge
            if orthogonal(v,w):
                edges.append((v,w))

    W = Sage_Graph(edges, format='list_of_edges')
    W.name("Large Witt graph")
    return W

def construct_truncated_Witt_graph():
    # get large witt graph and remove all vertices which start with a 1
    G = construct_large_Witt_graph()
    G.delete_vertices(filter( lambda x : x[0] == 1, G.vertices() ))
    G.relabel( lambda v: v[1:24] )

    G.name("Truncated Witt graph")
    return G

def construct_Grassman( const int q, const int n, const int input_e ):
    # this is too slow
    V = VectorSpace(Sage_GF(q),n) # vector space over F_q of dim n

    # get a generator of subspaces
    if n >= 2 * input_e:
        e = input_e
    else:
        e = n - input_e

    #add edges
    edges = []
    for W in V.subspaces(e):
        for U in V.subspaces(e):
            if W.intersection(U).dimension == e-1:
                edges.append( (W.basis_matrix(), U.basis_matrix()) )

    G = Sage_Graph(edges, format='list_of_edges')
    G.name("Grassman graph J_%d(%d,%d)" % (q, n, input_e) )
    return G
    

def get_classical_parameters_from_intersection_array( array, check=False):
    # we return the tuple (d,b,alpha,beta) representing the classical paramenters of the array passed
    # otherwise we return False
    # we use proposition 6.2.1 on page 195 of bouwer

    # b_i = arr[i]; c_i = arr[d - 1 + i]
    if check and len(array) % 2 != 0 : return False
    
    d = len(array) / 2

    def c_( const int i ) :
        if i == 0: return 0
        return array[d-1 + i]

    def b_( const int i ) :
        if i == d: return 0
        return array[i]

    def a_( const int i ):
        return array[0] - b_(i) - c_(i) 

    def getAlphaBeta(const int b):
        return  ( c_(2) / (b + 1) - 1, array[0] / q_binomial(d,1,q=b) )

    def checkValues(arr, const int d, const int b, alpha, beta):
        trial = intersection_array_from_classical_parameters(d, b, alpha, beta)
        for i in range(0, 2*d):
            if trial[i] != arr[i] : return False
        
        return True
    
    case1 = True # assume we are in the case a_i != a_1 * c_i
    for i in range(2,d): # yes, 2 is intentional
        # if a_i == a_1 * c_i
        if a_(i)  == a_(1) * c_(i): 
            case1 = False
            break
        
    if case1:
        # b = (a_2*c_3 - c_2*a_3)/(a_1*c_3 - a_3)
        b = ( a_(2) * c_(3) - c_(2) * a_(3)) / ( a_(1) * c_(3) - a_(3) )
    else :
        # b \in { c_2 - 1, -a_1 - 1}
        # try b = c_2 - 1
        b = c_(2) - 1
        (alpha,beta) = getAlphaBeta(b)
        if not checkValues(array, d, b, alpha, beta) : # then we must have b = -a_1 - 1
            b = -a_(1) - 1
    
    (alpha,beta) = getAlphaBeta(b)
    
    if check and not checkValues(array, d, b, alpha, beta): return False
    
    return (d, b, alpha, beta)


def distance_regular_graph_with_classical_parameters( const int d,
                                                      const int b,
                                                      const int alpha,
                                                      const int beta ):
    def is_power_of( const int num, const int base ):
        # this functions checks if num = base^k for some k in N and return k
        # if no such k exists, then -1 is returned
        cdef int baseToK = base
        cdef int k = 1
        #invariant : baseToK = base^k
        while ( baseToK < num ):
            baseToK *= base
            k += 1

        if baseToK == num:
            return k
        else:
            return -1
    # end is_power_of

    def q_of(const int num, const int exp ):
        # return prime power q s.t. num = q^exp
        # otherwise return -1
        (b,k) = is_prime_power(num, True)
        # if k != 0, then b^k = num
        # if k == 0, then num is not a prime power
        if k != 0 and (k % exp) == 0:
            # q^exp = b^k => q = b^i where i = k / exp
            return  b**(k/exp)
        else:
            return -1
    # end q_of

    assert d > 2, "only diameters >= 3"
    
    if b == 1 :
        if alpha == 1 and beta + d < 2 * d:
            # Johnson Graph
            return GraphGenerators.JohnsonGraph(beta+d, d)
        elif d == 3 and alpha == 4 and beta == 9:
            # Gosset graph
            return GraphGenerators.GossetGraph()
        elif alpha == 0 and beta + 1 >= d:
            # Hamming Graph
            n = beta + 1
            return GraphGenerators.HammingGraph(n,d)
        elif alpha == 2 and ( beta == 2*d + 1 or beta == 2*d - 1):
            # Halved cube graph
            if beta == 2*d +1: # then n = beta
                return construct_halved_cube(beta)
            else: # then n = beta + 1
                return construct_halved_cube(beta+1)
        else :
            assert False, "All distance regular graphs with classical parameters and b=1 are classified and I could not find what you are looking for"
            
    elif b == -2:
        if d == 3 and alpha == -4 and beta == 10:
            # large Witt graph
            return construct_large_Witt_graph()
        elif d == 3 and alpha == -2 and beta == 5:
            # truncate Witt graph
           return construct_truncated_Witt_graph()
        elif d == 3 and alpha == -3 and beta == 8:
            #goolay code graph
            return construct_extended_ternary_Golay_code_graph()
        pass
    
    elif b < 0 and is_prime_power(b):
        if alpha +1 == (1 + b*b)/(1 + b) and beta +1 == q_binomial(d+1,1,b):
            # U(2d,r) 
            pass
        elif d == 3 and alpha + 1 == 1 / (1+b) and beta + 1 == q_binomial(3,1,b):
            # Triality graph
            pass
        elif alpha + 1 == b and beta + 1 == b**d:
            #Hermitian form
            pass
        pass
    
    elif is_prime_power(b):
        if alpha == b and is_power_of( (beta +1)*(b-1)+1, b ) >= d+1:
            # we checked that beta + 1 = (b^(n-d+1) - 1)/(b - 1) for n >= 2d
            # Grassmann graph
            pass
        elif alpha == 0 and is_power_of( beta, b ) in {0, 0.5, 1, 1.5, 2}:
            # dual polar graphs
            pass
        elif ( q_of(b,2) != -1 and alpha + 1 == q_binomial(3, 1, q_of(b,2))
               and beta + 1 in { q_binomial(2*d+2, 1, q_of(b,2)),
                                 q_binomial(2*d, 1, q_of(b,2)) }
        ):
            # half dual polar graph or dist. 1 or 2 in sympletic dual polar graphs
            pass
        elif ( d == 3 and q_of(b,4) != -1 and alpha + 1 == q_binomial(5, 1, q_of(b,4))
               and beta + 1 == q_binomial( 10, 1, q_of(b,4))
        ):
            # Exceptional Lie graph or E_7(1)
            pass
        elif alpha + 1 == b and is_power_of( beta+1, b) >= d:
            # bilinear form
            pass
        elif ( q_of(b,2) != -1 and alpha + 1 == b
               and beta + 1 in { q_of(b,2)**(2*d-1), q_of(b,2)**(2*d+1) }
        ):
            # alternating form graphs or quadratic forms
            pass
        elif ( d == 3 and q_of(b,4) != -1 and alpha + 1 == b
               and beta + 1 == q_of(b,4)**9
        ):
            # affine E_6(q)
            pass
        pass
    #error
    pass
