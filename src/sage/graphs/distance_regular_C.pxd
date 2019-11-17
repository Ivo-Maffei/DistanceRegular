cdef extern from "sage/graphs/distance_regular_C/API.h":
	int HasVectorRank1(const int*, const unsigned int, const unsigned int)