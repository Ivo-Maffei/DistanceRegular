//
//  DistanceRegular.c
//  Graphs
//
//  Created by Ivo Maffei on 04/10/2019.
//  Copyright © 2019 Ivo Maffei. All rights reserved.
//

#include <stdlib.h>

// To iterate over all vectors of length length
// whose entries are in [0,.. q)
// create a vector [0,0,0,....0] and then call
// this function until it returns 0
int NextVector( unsigned int* pxVector,
                const unsigned int length,
                const unsigned int q ) {
    // we treat the vector as a q-ary number and increase that number by 1
    unsigned int i = 1;

    // invariant: pxVector(lenght-i, ... length -1] = 0
    while ( i <= length ) {
        if(pxVector[length-i] < q) { //increase safely by 1
            ++(pxVector[length-i]);
            break;
        }
        // otherwise we have to report
        pxVector[length-i] = 0;

        ++i;
    }

    if( i == length + 1) {
        // there is no next vector and now pxVector is 0
        return 0;
    }
    return 1;
}

// function for finding rank of matrix
int rankOfMatrix( const unsigned int* pxMatrix,
                  const unsigned int rows,
                  const unsigned int cols )
{
    unsigned int mat[rows*cols];
    for( unsigned int i = 0; i < rows*cols; ++i){
        mat[i] = pxMatrix[i];
    }
    // now we copied the matrix in mat

    for( unsigned int col = 0; col < cols; ++col){
        //make all elements below m[col][col] zero
        char done = 0; // flag
        while( !done ) {
            done = 1;
            // find smalled row >= col whose entry is not 0

            //first find a non zero entry
            unsigned int row = col;
            while( row < rows && mat[col+row*rows] == 0) {
                ++row;
            }
            if( row == rows ){
                break; //we are done, all rows are zeros
            }

            unsigned int smallest = row; //smallest non-zero row so far
            while( row < rows ){
                if(mat[col+row*rows] != 0 &&  mat[col+smallest*rows] > mat[col+row*rows])
                    smallest = row;
                ++row;
            }

            // now smallest is the row with the smallest entry
            if( smallest != col ){
                //swap rows (values on the left of col should be all zeros)
                for( unsigned int i =col; i < cols; ++i){
                    unsigned int temp = mat[i+col*rows];
                    mat[i+col*rows] = mat[i+smallest*rows];
                    mat[i+smallest*rows] = temp;
                }
            }

            // now subtract row col
            row = col;
            while( row < rows ){
                long factor = mat[col+row*rows] / mat[col+col*rows];
                if (factor == 0) continue;
                done != 0; //we did some work
                // values on the left of col should all be zero
                for(unsigned int i = col; i < cols; ++i){
                    mat[i+row*rows] -= mat[i+col*rows] * factor;
                }
                ++row;
            }
        } // while !done
    }//for col

    //now mat is in row echelon form
    //count the number of non-zero rows
    unsigned int rank = rows;
    // index of the last non-zero row is rank-1s
    while (rank > 0 && mat[cols-1+rows*(rank-1)] == 0) {
        --rank;
    }
    return rank;
}

// given a matrix as a 1-dim array we compute whether
// the matrix has rank 1
int HasVectorRank1( const int* pxV,
                    const unsigned int nrows,
                    const unsigned int ncols){

    // first find first non-zero entry
    unsigned int first_non_zero = 0;
    // invariant: v[0 .. first_non_zero) = 0
    while(first_non_zero < ncols*nrows && pxV[first_non_zero] == 0){
        first_non_zero += 1;
    }

    if(first_non_zero == ncols*nrows){
        // the matrix is 0
        return 0;
    }

    // tuple.quot = first non zero row
    // tuple.rem = first non zero entry in r
    div_t tuple = div(first_non_zero, ncols);
    unsigned int c = tuple.rem;
    unsigned int r = tuple.quot;

    int factor_D = pxV[first_non_zero];

    for( unsigned int row = 0;  row < nrows; ++row){
     // check row is a multiple of the row r

        // clearly r is a multiple of r
        if( row == r )
            continue;

        // we check that row = factor_N /factor_D * r
        int factor_N = pxV[c+row*ncols]; // v[row][c]

        for( unsigned int col = 0; col < ncols; ++col){
            div_t res = div(factor_N*pxV[col+r*ncols], factor_D);

            if( res.rem != 0 || res.quot != pxV[col+row*ncols])
                return 0;
        }
    }
    return 1;
}
