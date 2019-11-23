# distutils: sources = sage/graphs/distance_regular_C/Core/DistanceRegular.c
# distutils: include_dirs = sage/graphs/distance_regular_C/
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
cimport sage.graphs.distance_regular_C as c_code #not used atm
from cysignals.signals cimport sig_check
from libc.stdlib cimport malloc, free

# python imports
from math import ceil, floor
import numpy as np
from collections import deque as queue

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

def profilingCython( const int repetitions=10 ):
    import time

    sumTime = 0
    sum2Time = 0

    length = 9
    q = 7
    
    vecs = _AllVectorsIter(length,[i for i in range(0,q)])
    vecs1 = _AllVectorsIter(length,[i for i in Sage_GF(q)])
    w = tuple([0 for i in range(0,length)])

    elems = [x for x in Sage_GF(q)]
    
    tableSum = [ [0 for i in range(0,q)] for i in range(0,q)]
    for i in range(0,q):
        for j in range(0,q):
            x = elems[i]
            y = elems[j]
            z = x+y
            k= 0
            while elems[k] != z:
                k += 1
            tableSum[i][j] = k
        
    
    
    for rep in range(0,repetitions):

        
        start = time.time()
        l = [w]
        for v in vecs:
            sig_check()
            w = _add_vectors_over_q(tableSum,v,w)
            l.append(w)
        end = time.time()
        sumTime += end-start
        print("sumTime %.6f" %sumTime)
       

        start = time.time()
        l = [w]
        for v in vecs1:
            sig_check()
            w = _add_vectors(v,w)
            l.append(w)
        end = time.time()
        sum2Time += end-start
        print("sumTime2 %.6f" %sum2Time)

    print("sum vectors of len %d in GF(%d) in  %.6f time(avg)" %(length, q, sum2Time / repetitions ))
    print("sum vectors of len %d in GF(%d) with tables in %.6f time(avg)" %(length, q, sumTime / repetitions ))    

#an iterator to iterate over all vectors of length n using the elements given
class _AllVectorsIter:
    def __init__(self, n, elemsIterator ):
        self.elems = []
        for i in elemsIterator:
            if i not in self.elems:
                self.elems.append(i)

        # now self.elems is a list of all the elements passed without duplication
        self.length = n
        self.elemsLength = len(self.elems)

    def __iter__(self):
        self.start = True #this means to start fresh
        return self

    def __next__(self): # this is python 3
        return self.next(self)

    def next(self): # this is python 2
        if self.start:
            self.start = False
            self.last = [0 for i in range(0,self.length) ] # this represents a number base self.elemsLength
            return [ self.elems[0] for i in range(0,self.length)]
        else:
            for i in range(self.length-1, -1, -1):
                self.last[i] += 1
                if self.last[i] != self.elemsLength:
                    break
                self.last[i] = 0
            # now we increased self.last by 1

            for i in self.last:
                if i != 0:
                    break
                
            else: # we didn't break, so self.last is 0 vector
                self.start = True
                raise StopIteration

            converted = []
            for i in self.last:
                converted.append(self.elems[i])
                
            return converted
        
    def __len__(self):
        return self.elemsLength**(self.length)
# end of class
            
def _convert_vector_to_F_q(v,const int q):
    # takes a vector over ZZ_q and convertes it
    # to a vector over GF(q)
    # the map used is not a homomorphism!!!
    # we rely on the fact that iterating over finite fields always
    # happens in the same order
    
    field = Sage_GF(q)
    fieldElements = []
    for i in field:
        fieldElements.append(i)

    newVector = map( lambda x : fieldElements[x], v)
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
    assert len(v) == len(w), "Can't compute Hamming distance of 2 vectors of different size!"
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

    allMatrices = IntegerVectors(length=d*e,max_part=q-1)

    matricesOverq = _AllVectorsIter( d*e, [x for x in Sage_GF(q)] ) #map( lambda x: _convert_vector_to_F_q(x,q), allMatrices)

    rank1Matrices = []
    for v in matricesOverq:
        sig_check()
        if Sage_Matrix(v, nrows=d).rank() == 1:
            rank1Matrices.append(v)

    edges = []
    for v in matricesOverq:
        for w in rank1Matrices:
            sig_check() # this loop may take a long time, so check for interrupts
            edges.append( ( tuple(v), _add_vectors(v,w) ) )
    
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

    import time

    start = time.time()
    
    field = Sage_GF(q)
    elemsField = []
    for x in field:
        elemsField.append(x)

    tableSum = [[0 for i in range(0,q)] for i in range(0,q) ]
    for i in range(0,q):
        for j in range(0,q):
            x = elemsField[i]
            y = elemsField[j]
            z = x + y

            # find k s.t. elmesField[k] = z
            k = 0
            while True:
                if elemsField[k] == z:
                    break
                k += 1
            
            tableSum[i][j] = k

    tableNegation = [ 0 for i in range(0,q)]
    for i in range(0,q):
        x = elemsField[i]
        z = -x

        k = 0
        while True:
            if elemsField[k] == z:
                break
            k += 1

        tableNegation[i] = k

    end = time.time()
    print("%.6f s to create tables" %(end-start))

    # now elemsField[i] + elemsField[j] = elemsField[tableSum[i][j]]
    # and -elemsField[i] = elemsField[tableNegation[i]]

    skewSymmetricMatrices = IntegerVectors(length=(n*(n-1))/2, max_part=q-1) #_AllVectorsIter((n*(n-1))/2, elemsField)


    start = time.time()
    
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
            actualRow = []
            for entry in row:
                actualRow.append(elemsField[entry])
            actualMat.append(actualRow)
        
        # finally check if mat is a rank2 matrix
        if Sage_Matrix(Sage_GF(q),actualMat).rank() == 2:
            rank2Matrices.append(v) # we append v as it is smaller than mat

    end = time.time()
    print("%.6f s to find %d rank 2 matrices" %(end-start, len(rank2Matrices)))


    start = time.time()
    
    edges = []
    count = 0
    limit = q**(n*(n-1) / 2) // 20
    for v in skewSymmetricMatrices:
        count += 1
        if count > limit:
            print("lap %.6f" %(time.time()-start))
            count = 0
        
        for w in rank2Matrices:
            sig_check() # check for interrupts
            edges.append(( tuple(v), _add_vectors_over_q(tableSum,v,w) ))
            #G.add_edge( (tuple(v), _add_vectors(v,w)) )

    end = time.time()
    print("%.6f s to find edges" %(end-start))
            
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

    # this is the bar automorphism on GF(q)
    def bar( x ):
        return x**r

    FqElems= []
    for x in Sage_GF(q):
        FqElems.append(x)

    FrElems = []
    for x in Sage_GF(r):
        FrElems.append(x)
        
    # find all hermitean matrices
    # we need the upper half and the diagonal
    allUpperHalves = _AllVectorsIter( (n*(n-1))/2, FqElems)
    allDiagonals = _AllVectorsIter(n, FrElems)

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
                    mat[r][c] = bar(mat[c][r])

            # now mat is a matrix
            if Sage_Matrix(Sage_GF(q),mat).rank() == 1:
                rank1Matrices.append( (diag, up) ) # no need to store the whole matrix

    edges = []
    for up in allUpperHalves:
        for diag in allDiagonals:
            for (d,u) in rank1Matrices:
                sig_check()
                edges.append(  ( (tuple(diag),tuple(up)), (_add_vectors(diag,d), _add_vectors(up,u)) )  )
                
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
