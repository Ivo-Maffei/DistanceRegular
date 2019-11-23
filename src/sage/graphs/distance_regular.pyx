# cython: profile=True
# -*- coding: utf-8 -*-
r"""
This module aims at constructing distance-regular graphs.

This module provide the construction of several distance-regular graphs.
In addition we implemented multiple utility functions for such graphs.


EXAMPLES::

<Lots and lots of examples>

AUTHORS:

- Ivo Maffei (2005-01-03): initial version

"""

# ****************************************************************************
#       Copyright (C) 2013 Ivo Maffei <ivomaffei@gmail.com>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

# project C import
from cysignals.signals cimport sig_check

# python imports
import numpy as np

# sage imports
from sage.graphs.graph_generators import GraphGenerators
from sage.graphs.graph import Graph as Sage_Graph
from sage.arith.misc import is_prime_power
from sage.combinat.q_analogues import q_binomial
from sage.combinat.integer_vector import IntegerVectors
from sage.modules.free_module import VectorSpace
from sage.rings.finite_rings.finite_field_constructor import GF as Sage_GF
from sage.matrix.constructor import Matrix as Sage_Matrix
from sage.rings.rational cimport Rational

################################################################################
# UTILITY FUNCTIONS

def iteratorSpeedTest(n,q):
    r"""
    input n,q.

    appends to a empty list all vectors of length n with entries [0..q)
    
    it does the above with _AllIntegerVectrosIter and IntegerVectors
    it prints the time taken

    _AllIntegerVectorsIter is way faster (0.7s vs 35s)
    """
    import time
    
    start = time.time()
    l = []
    vecs = _AllIntegerVectorsIter(n,q)
    for v in vecs:
        l.append(v)
    end = time.time()
    print("my vectors iterator %.6f (%d vectors)" %(end-start, len(l)) )

    start = time.time()
    l2 = []
    vecs2 = IntegerVectors(length=n,max_part=q-1)
    for v in vecs2:
        l2.append(v)
    end = time.time()
    print("sage vectors iterator %.6f (%d vectors)" %(end-start, len(l2)) )

def sumSpeedTest(n,q):
    """
    result is that the speed is basically the same, but this crap is slow!!!
    n = 10^7 is roughly  3.5 s

    (should try using C)
    """
    import time

    start = time.time()
    fieldElems = _get_elems_of_GF(q)
    sumTable = _get_sum_table(fieldElems)
    end = time.time()
    print("created tables in %.6f"%(end-start))

    start = time.time()
    x = fieldElems[0]
    for i in range(0,n):
        sig_check()
        y = fieldElems[i % q]
        x += y
    end = time.time()
    print("summed %d elems over GF(%d) in %.6f"%(n,q,end-start))

    start = time.time()
    cdef int x1 = 0
    cdef int y1 = 0
    for i in range(0,n):
        sig_check()
        y1 = i % q
        x1 = sumTable[x1][y1]
    end = time.time()
    print("summed %d elems over GF(%d) in %.6f using tables"%(n,q,end-start))

def listSumSpeedTest(n,q):
    r"""
    not surprisingly the first is way quicker (roughly half of the time)
    """
    import time

    start = time.time()
    fieldElems = _get_elems_of_GF(q)
    sumTable = _get_sum_table(fieldElems)
    end = time.time()
    print("created tables in %.6f"%(end-start))

    vecs = _AllIntegerVectorsIter(n,q)

    start = time.time()
    x = tuple([0 for i in range(0,n)])
    l = []
    for v in vecs:
        sig_check()
        x = _add_vectors_over_q(sumTable,x,v)
        l.append(x)
    end = time.time()
    print("summed %d vectors of length %d over GF(%d) in %.6f using tables"%(q**n,n,q,end-start))

    start = time.time()
    x = tuple([fieldElems[0] for i in range(0,n)])
    l = []
    for v in vecs:
        sig_check()
        y = _convert_vector_to_GF_q(v,fieldElems)
        x = _add_vectors(x,y)
        l.append(x)
    end = time.time()
    print("summed %d vectors of length %d over GF(%d) in %.6f"%(q**n,n,q,end-start))
    

#an iterator to iterate over all vectors of length n using the elements given
class _AllIntegerVectorsIter:
    def __init__(self, const int n, const int q ):
        self.q = q
        self.n = n

    def __iter__(self):
        self.start = True #this means to start fresh
        return self

    def __next__(self): # this is python 3
        return self.next(self)

    def next(self): # this is python 2
        if self.start:
            self.start = False
            self.last = [0 for i in range(0,self.n) ]
        else:
            for i in range(self.n-1, -1, -1):
                self.last[i] += 1
                if self.last[i] != self.q:
                    break
                self.last[i] = 0
            # now we increased self.last by 1

            else: # we didn't break, so self.last is 0 vector
                self.start = True
                raise StopIteration

        # both branches return self.last
        return tuple(self.last)

    def __len__(self):
        return self.q**(self.n)
# end of class

def _get_elems_of_GF( const int q):
    elems = []

    for x in Sage_GF(q):
        elems.append(x)

    return elems

def _get_sum_table( elems ):
    cdef int n = len(elems)

    table = [ [0 for i in range(0,n)] for j in range(0,n) ]
    for i in range(0,n):
        for j in range(0,n):
            x = elems[i]
            y = elems[j]
            z = x+y

            k = 0
            while elems[k] != z:
                k += 1

            table[i][j] = k

    return table
            
def _convert_vector_to_GF_q(v,elems):
    r"""
    Applies the map ``i`` $\mapsto$ ``elems[i]`` to ``v``
    """
    
    newVector = []
    for i in v:
        newVector.append(elems[i])
        
    return newVector

def _add_vectors(v, w):
    cdef int n = len(v)
    
    result = []
    for i in range(0,n):
        result.append( v[i] + w[i] )
        
    return tuple(result)

def _add_vectors_over_q(table, v, w):
    cdef int n = len(v)

    result = []
    for i in range(0,n):
        result.append( table[v[i]][w[i]] )

    return tuple(result)

def _hamming_weight( codeword ):
    cdef int weight = 0
    for i in codeword:
        if i != 0: weight += 1
        
    return weight

def _hamming_distance( v, w ):
    assert( len(v) == len(w),
         "Can't compute Hamming distance of 2 vectors of different size!")
         
    cdef int counter = 0
    for i in range(0, len(v)):
        if ( v[i] != w[i] ):
            counter = counter + 1
    
    return counter

def _codewords_have_different_support( vec1, vec2 ):
    # the support of a codeword is the set of coordinates where the codeword
    # has non-zero entries
    for (i,j) in zip(vec1,vec2):
        if i*j != 0:
            return False
    return True
    

################################################################################
# START CONSTRUCTIONS

def construct_bilinear_form_graph(const int d, const int e, const int q):
    r"""
    Return a bilienar form graph with the given parameters.

    This build a graph whose vertices are all ``d``x``e`` matrices over
    ``GF(q)``. 2 vertices are adjecent if the difference of the 2 
    matrices has rank 1.

    INPUT:

    - ``d,e`` -- integers
    - ``q`` -- a prime power

    EXAMPLES:

    TESTS::
    
    """
    matricesOverq = _AllIntegerVectorsIter( d*e, q )
    fieldElems = _get_elems_of_GF(q)
    sumTable = _get_sum_table(fieldElems)

    rank1Matrices = []
    for v in matricesOverq:
        sig_check()
        w =  _convert_vector_to_GF_q(v,fieldElems)
        if Sage_Matrix(Sage_GF(q), w, nrows=d).rank() == 1:
            rank1Matrices.append(v)

    edges = []
    for v in matricesOverq:
        for w in rank1Matrices:
            sig_check() # this loop may take a long time, so check for interrupts
            edges.append( ( v, _add_vectors_over_q(sumTable,v,w) ) )
    
    G = Sage_Graph(edges, format='list_of_edges')    
    G.name("Bilinear form graphs over F_%d with parameters (%d,%d)" %(q,d,e) )
    return G

def construct_alternating_form_graph(const int n, const int q):
    r"""
    Return the alternating form graph with the given parameters.

    This construct a graph whose vertices are all ``n``x``n`` skew symmetric
    matrices over ``GF(q)``. 2 vertices are adjecent if and only if the
    difference of the 2 matrices has rank 2

    INPUT:

    - ``n`` -- integer
    - ``q`` -- prime power

    EXAMPLES:

        sage: g = construct_alternating_form_graph(5,2)
        sage: g.is_distance_regular()
        True

    TESTS::

    """

    
    field = Sage_GF(q)
    fieldElems = _get_elems_of_GF(q)
    sumTable = _get_sum_table(fieldElems)

    tableNegation = [ 0 for i in range(0,q)]
    for i in range(0,q):
        x = fieldElems[i]
        z = -x

        k = 0
        while fieldElems[k] != z:
            k += 1

        tableNegation[i] = k

    # now fieldElems[i] + fieldElems[j] = fieldElems[sumTable[i][j]]
    # and -fieldElems[i] = fieldElems[tableNegation[i]]

    skewSymmetricMatrices = _AllIntegerVectorsIter( (n*(n-1))/2, q)
    
    rank2Matrices = []
    for v in skewSymmetricMatrices:
        sig_check()
        
        # we need to convert v into a matrix
        
        data = n-1 # how much data to take from v
        index = 0 # where are we in v
        zeros = [ 0 for i in range(0,n) ] # row of zeros
        mat = [] # v into matrix form
        while data >= 0:
            row = zeros[:n-data] + v[index:index+data]
            index = index + data
            data -= 1
            mat.append(row)
        # now mat is upper triangular with entries from v
        # so we need to fill the lower half
        for r in range(1,n): #skip first row which is fine
            for c in range(0,r): # in the bottom half
                mat[r][c] = tableNegation[mat[c][r]]

        #convert mat to GF(q)
        actualMat = []
        for row in mat:
            actualMat.append(_convert_vector_to_GF_q(row, fieldElems))
        
        # finally check if mat is a rank2 matrix
        if Sage_Matrix(Sage_GF(q),actualMat).rank() == 2:
            rank2Matrices.append(v) # we append v as it is smaller than mat

    # now we have all matrices of rank 2
    
    edges = []
    for v in skewSymmetricMatrices:    
        for w in rank2Matrices:
            sig_check() # check for interrupts
            edges.append(( tuple(v), _add_vectors_over_q(sumTable,v,w) ))

    G = Sage_Graph(edges, format='list_of_edges')
    G.name("Alternating form graph on (F_%d)^%d" %(q,n) )
    return G

def construct_hermitean_form_graph(const int n, const int q):
    r"""
    Return the Hermitean from graph with the given parameters.

    We build a graph whose vertices are all ``n``x``n`` Hermitean matrices
    over ``GF(q)``. 2 vertices are adjecent if the difference of the 2 vertices
    has rank 1. We need ``q``=``r**2`` for some prime power ``r``

    INPUT:

    - ``n`` -- integer
    - ``q`` -- prime power

    EXAMPLES:

        sage: g = construct_hermitean_form_graph(5,2)
        sage: g.is_distance_regular()
        True

    .. NOTES::
    
        If ``q`` does not satisfy the requirements, then this function
        will raise a ``ValueError``.
      
    TESTS::

    """
    
    (b,k) = is_prime_power(q, True)
    if k == 0 or k % 2 != 0:
        raise ValueError("We need q=r^2 where r is a prime power")

    # here we have b^k = q, b is prime and k is even
    r = b**(k/2)
    # so r^2 = b^k = q

    FqElems= _get_elems_of_GF(q)
    sumTableq = _get_sum_table(FqElems)
    
    FrElems = _get_elems_of_GF(r)
    sumTabler = _get_sum_table(FrElems)

    barTable = []
    for i in range(0,q):
        x = FqElems[i]
        z = x**r
        k = 0
        while FqElems[k] != z:
            k += 1
        barTable[i] = k
    # FqElems[i]**r = FqElems[barTable[i]]
    
    # find all hermitean matrices
    # we need the upper half and the diagonal
    allUpperHalves = _AllIntegerVectorsIter( (n*(n-1))/2, q)
    allDiagonals = _AllIntegerVectorsIter(n, r)

    rank1Matrices = []
    for up in allUpperHalves:
        for diag in allDiagonals:
            # compose the matrix
            sig_check()

            data = n-1 # how much data to take from v
            index = 0 # where are we in v
            zeros = [ 0 for i in range(0,n) ] # row of zeros
            mat = [] # v into matrix form
            while data >= 0:
                row = zeros[:n-data-1] + diag[index] + up[index:index+data]
                index = index + data
                data -= 1
                mat.append(row)
            # now mat is upper triangular with entries from up
            # so we need to fill the lower half
            for r in range(1,n): #skip first row which is fine
                for c in range(0,r): # in the bottom half
                    mat[r][c] = barTable[mat[c][r]]

            # now convert mat !!!THIS IS WRONG WE TREAT DIAGONAL AS F_q INSTEAD OF F_r
            actualMat = []
            for row in mat:
                actualMat.append(_convert_vector_to_GF_q(row,FqElems))

            # now mat is a matrix
            if Sage_Matrix(Sage_GF(q), actualMat).rank() == 1:
                rank1Matrices.append( (diag, up) ) # no need to store the whole matrix

    edges = []
    for up in allUpperHalves:
        for diag in allDiagonals:
            for (d,u) in rank1Matrices:
                sig_check()
                edges.append(  ( (tuple(diag),tuple(up)), (_add_vectors_over_q(sumTableq,diag,d), _add_vectors(sumTableq,up,u)) )  )
                
    G = Sage_Graph(edges, format='list_of_edges')
    G.name("Hermitean form graph on (F_%d)^%d" %(q,n) )
    return G

def construct_halved_cube( int n ):
    r"""
    Return the graph $\frac 1 2 Q_n$.

    This builds the halved cube graph in ``n`` dimensions.
    The construction is iterative, so the vertices label have no meaning.
    
    INPUT:

    - ``n`` -- integer

    EXAMPLES:

        sage: g = construct_halved_cube(8) # long time for large n

        # n = 14 -> ~1min
        # n = 15 -> ~4min

        sage: g.is_distance_regular()
        True

    TESTS::

    """
    #construct the halved cube graph 1/2 Q_n ( = Q_{n-1} ^2 )
    G = GraphGenerators.CubeGraph(n-1)
    # now square the graph
    # we use the fact that the vertices are strings and their distance is their hamming_distance
    for i in G.vertices():
        for j in G.vertices():
            sig_check()
            if _hamming_distance(i, j) == 2 :
                G.add_edge(i,j)
                
    G.relabel() # label back vertices to 0,1,2,...

    G.name("Halved %d Cube"%n)
    return G

def construct_extended_ternary_Golay_code_graph():
    r"""
    Return the graph associated with the extended ternary Golay code.

    The graph constructed has  the codewords of
    the extended ternary Golay code as vertices.
    2 vertices are adjecent if their difference is a codeword of
    hamming weight 12.

    EXAMPLES:

        sage: g = construct_extended_ternary_Golay_code_graph()
        sage: g.is_distance_regular()
        True

    TESTS::
    """

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
    r"""
    Return the large Witt graph.

    This builds the large Witt graph. Each vertex represents a codeword.

    EXAMPLES:

        sage: g = construct_large_Witt_graph()
        sage: g.is_distance_regular()
        True

    TESTS::

    """
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
    
    vertices=[]
    # we will add tuples as vertices via add_vertex(tuple([1,0,1....]))
    cdef int vertices_found = 0 #max is 759
    for vec in IntegerVectors(k=12,max_part=1): #iterate over all binary vectors of size 12
        codeword = np.matmul(vec,G) % 2
        if (_hamming_weight(codeword) == 8 ): # is a valid vertex
            vertices.append(tuple(codeword))
            vertices_found += 1
            if vertices_found == 759: break

    edges = []
    # here W contains all 759 vertices
    for v in vertices:
        for w in vertices:
            # check if w,v are orthogonal and if so, add edge
            if _codewords_have_different_support(v,w):
                edges.append((v,w))

    W = Sage_Graph(edges, format='list_of_edges')
    W.name("Large Witt graph")
    return W

def construct_truncated_Witt_graph():
    r"""
    Return the truncated Witt graph.

    This builds the large Witt graph, then removes
    all vertices whose codeword start with a 1.

    EXAMPLES:

        sage: g = construct_large_Witt_graph()
        sage: g.is_distance_regular()
        True

    TESTS::

        sage: g = construct_large_Witt_graph()
        ...
    """
    # get large witt graph and remove all vertices which start with a 1
    G = construct_large_Witt_graph()
    G.delete_vertices(filter( lambda x : x[0] == 1, G.vertices() ))
    G.relabel( lambda v: v[1:24] )

    G.name("Truncated Witt graph")
    return G

def construct_Grassman( const int q, const int n, const int input_e ):
    r"""

    Return a Grassman graph with parameters ``(q,n,e)``.

    This build the Grassman graph $J_q(n,e)$. That is, for a vector
    space $V = \mathbb F(q))^n$ the output is a graph on the subspaces
    of dimension $e$ where 2 subspaces are adjancent if their intersection
    has dimension $e-1$.

    INPUT:
   
    - ``q`` -- a prime power
    - ``n, e`` -- integers with ``n >= e``

    EXAMPLES:

        tbd

    TESTS::

        tbd

    """
    if n < input_e:
        raise ValueError(
            "Impossible parameters n > e (%d > %d)" %(n,input_e) )
    
    V = VectorSpace(Sage_GF(q),n) # vector space over F_q of dim n

    # get a generator of subspaces
    if n >= 2 * input_e:
        e = input_e
    else:
        e = n - input_e

    #add edges
    edges = []

    # in order to find U s.t. W intersection U has dim e-1
    # we pick S of dim e-1 in W
    # we pick v not in W ( we pick the lift of v in V/W)
    # and let U = span(v,S)
    for W in V.subspaces(e):
        for S in W.subspaces(e-1):
            # get a basis of S
            basis = []
            for v in S.basis():
                basis.append(v)

            # now get elements not in W
            quotientW = V.quotient(W)
            for w in quotientW[1:]: #we skip the first vector which is 0
                v = quotientW.lift(w)
                basis.append(v)
                U = V.span( basis )
                
                edges.append( (W.basis_matrix(), U.basis_matrix()) )
                # now remove v fom basis
                basis.pop()

    G = Sage_Graph(edges, format='list_of_edges')
    G.name("Grassman graph J_%d(%d,%d)" % (q, n, input_e) )
    return G

# END CONSTRUCTIONS
################################################################################

# given a graph G it halves the graph
def halve_graph(G) :
    r"""
    Return a half of this graph.

    Given a graph $G$ which is assumed to be bipartite,
    this function returns a graph $H$ which is half of $G$.
    That is, $H$ is a subgraph of $G$ consisting of all vertices in one
    of the 2 distinct partitions of G where $x,y \in H$ are
    adjecent if and only if $d(x,y) = 2$ in $G$.

    INPUT:

    - ``G`` : a bipartite graph

    EXAMPLES:

        tbd

    ..NOTE::
    
        This function will raise a ``ValueError``
        if the input graph is not bipartite.

    TESTS::
    """
    
    if not G.is_bipartite():
        raise ValueError(
            "The input graph is not bipartite")
    
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

# from bouwer book, we assume d \gt 3 [not sure if it works with smaller d]
def intersection_array_from_classical_parameters( const int d,
                                                  const int b,
                                                  const float alpha,
                                                  const float beta ):
    r"""
    Return the intersection array generated by the input.

    The input represents the classical parameters $(d,b,\alpha,\beta)$.
    The result is the intersection array of a possible graph with such parameters.
    Note that we don't check for the existance of such graph.

    INPUT:
    - ``d, b`` -- integers
    - ``alpha, beta`` -- numbers

    EXAMPLES:

        tbd

    ..NOTE::
    
        Atm we don't knwo if this works for d< 3

    TESTS::

        tbd
    """
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
            # 1+ \a \frac {b^{i-1} - 1}{b - 1}
            c = 1 + alpha * ( btoi - 1 ) * invb
            btoi = btoi * b
            c = c * (btoi - 1) * invb # c = c_i
            cs.append( c )
            bs.append( invb * (btod - btoi) * (beta - alpha*(btoi - 1)*invb) )
            
    # now we need to add c_d to cs
    if b == 1:
        cs.append( d * (1 + alpha * (d - 1)) )
    else :
        c = 1 + alpha * ( btoi - 1 ) * invb # 1+ \a \frac {b^{d-1} - 1}{b - 1}
        c = c * (btod - 1) * invb # c = c_d
        cs.append( c )
    return (bs + cs)

def intersection_array_from_graph( G ):
    r"""
    Return the intersection array of this graph.

    This function is a simple wrapper around 
    :meth:`sage.graphs.distances_all_pairs.is_distance_regular`
    but it returns the intersection array
    $\{b_0,...,b_{d-1},c_1,...,c_d\}$.
    If the input is not a distance-regular graph, then
    a ``ValueError`` is raised.

    INPUT:
    
    - ``G`` -- a distance-regular graph

    EXAMPLES:

        tbd
    
    ..NOTE::

        A ``ValueError`` will be raised if the input graph is not
        distance-regular.
    """
    t = G.is_distance_regular(True)
    if not t:
        raise ValueError("the graph passed is not distance_regular")
    (b,c) = t
    # annoyingly b ends with None (b_d = 0)
    # and c starts with None (c_0 = 0)
    # so trim these 2 values
    return b[:-1]+c[1:]

# check if the graph G is a grassman graph
def is_Grassman( G ):
    if not G.is_distance_regular(): return False
    intArr = intersection_array_from_graph(G)
    # If G is Grassman, then we can deduce the classical paramaters from the intersection array
    (d, b, alpha, beta) = get_classical_parameters_from_intersection_array(intArr, True)

    # as an aside we don't really need to check whether b is a prime power
    # b == alpha && b != 1 && b > 0 is enough 
    return d > 2 and b == alpha and b != 1 and b > 0    

def get_classical_parameters_from_intersection_array( array, check=False):
    r"""
    Return the classical parameters ``(d,b,alpha,beta)`` 
    representing the intersection array.

    This function will check whether given array is an itersection array 
    that can be represented with classical parameters.
    You can disable these extra checks, by setting the optional check input
    to ``False``

    INPUT:

    - ``array`` -- array of integers
    - ``check`` -- boolean; if ``False`` this function will assume that 
      ``array`` is a valid intersection array

    OUTPUT:
    
    tuple ``(d,b,alpha,beta)`` of classical parameters for array.

    EXAMPLES:

        tbd

    ALGORITHM:

    This algorithm takes advantage of theorem 6.2.1 on page 195 of bouwer book
    

    .. NOTE::

        This function may raise a ``ValueError`` if ``check`` is set to ``True``.

    TESTS::

        tbd

    """
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
        if not checkValues(array, d, b, alpha, beta) :
            # then we must have b = -a_1 - 1
            b = -a_(1) - 1
    
    (alpha,beta) = getAlphaBeta(b)
    
    if check and not checkValues(array, d, b, alpha, beta):
        raise ValueError(
            "Input array can't be represented with classical parameters")
    
    return (d, b, alpha, beta)

def distance_regular_graph_with_classical_parameters( const int d,
                                                      const int b,
                                                      const int alpha,
                                                      const int beta ):
    r"""
    Return a distance-regular graph $G$ with the given classical parameters.

    We assume $d \geq 3$.
    If no distance-regular graph satisfying the input parameters is found,
    then this function will raise a ValueError

    INPUT:

    - ``d`` -- integer; we assume this is greater or equal than 3
    - ``b`` -- integer
    - ``alpha, beta`` -- numbers

    OUTPUT:
    
    A distance-regular graph $G$ with classical parameters ``(d,b,alpha,beta)``

    EXAMPLES::
    
        sage: g = distance_regulat_graph_with_classical_parameters(3,-2,-4,10)
        sage: g.is_distance_regular()
        True
        sage: a = intersection_array_from_graph(g)
        sage: get_classical_parameters_from_intersection_array(a)
        (3,-2,-4,10)0
    
    .. NOTE::
    
        The outputted graph is NOT unique. There might be another graph with
        the given classical parameters. However this function is deterministic,
        i.e. it will always output the same graph given the same input.

    TESTS::

        tbd

    """
    
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

    if d < 3:
        raise ValueError(
            "We only consider distance-regular graphs with diameter >=3")
    
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
            raise ValueError(
                "No distance-regular graph with the given parameters exists")
            
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
        elif ( d == 3 and q_of(b,4) != -1
               and alpha + 1 == q_binomial(5, 1, q_of(b,4))
               and beta + 1 == q_binomial( 10, 1, q_of(b,4))
        ):
            # Exceptional Lie graph or E_7(1)
            pass
        elif alpha + 1 == b and is_power_of( beta+1, b) >= d:
            # bilinear form
            e = is_power_of(beta+1, b)
            return construct_bilinear_form_graph(d,e,b)
        elif ( q_of(b,2) != -1 and alpha + 1 == b
               and beta + 1 in { q_of(b,2)**(2*d-1), q_of(b,2)**(2*d+1) }
        ):
            # alternating form graphs or quadratic forms
            q = q_of(b,2)
            if beta + 1 == q**(2*d-1):
                n = 2*d
            else:
                n = 2*d+1
            return construct_alternating_form_graph(n,q)
        elif ( d == 3 and q_of(b,4) != -1 and alpha + 1 == b
               and beta + 1 == q_of(b,4)**9
        ):
            # affine E_6(q)
            pass
        pass

    raise ValueError(
        "Can't find a distance-regular graph with the given parameters")
