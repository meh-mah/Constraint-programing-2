/*
 * Authors M&M
 */
#include <gecode/driver.hh>
#include <gecode/int.hh>
#include <gecode/minimodel.hh>
#include <cmath>
#include <iostream>
#include "no-overlap.h"


class SquarePacking : public Script {
public:
    /*
     * size s of the surrounding square
     */
  IntVar s;
  
  /*
   * integer variables which give the respective x and y coordinates for each square to be packed
   */
  IntVarArray X;
  IntVarArray Y;
  
  enum {
      MODEL_REIFY, MODEL_NOOVERLAP
  };

  SquarePacking(const SizeOptions& so) : 
  
  X(*this, so.size()-1, 0, ((so.size()*(so.size()+1))/2)), 
  Y(*this, so.size()-1, 0, ((so.size()*(so.size()+1))/2)),
          
  // problem decomposition according to the given formula in section 2.1
  s(*this, ceil(sqrt((so.size()*(so.size()+1)*(2*so.size()+1))/6)), ((so.size()*(so.size()+1))/2))
  {

    int no_of_squares = so.size();
    int S1, S2, si;
      
      switch (so.model()){
          
          /*
           * part 2: Express with reification that no two squares overlap.
           * Two squares s1 and s2 do not overlap, iff
           * (a) s1 is left of s2, or
           * (b) s2 is left of s1, or
           * (c) s1 is above s2, or
           * (d) s2 is above s1.
           */
          case MODEL_REIFY:
          {
              std::cout<<"Using reified constraints : "<<std::endl;
              for(int k = 0; k < no_of_squares-1; k++)
              {
                  for(int l = 0; l < no_of_squares-1; l++)
                  {
                      if(k < l)
                      {
                          S1 = size(no_of_squares,k);
                          S2 = size(no_of_squares,l);
                          IntVar X1(X[k]);
                          IntVar Y1(Y[k]);
                          IntVar X2(X[l]);
                          IntVar Y2(Y[l]);
                          rel(*this, (X1 +  S1 <= X2) ||
                                  (X2 +  S2 <= X1) || 
                                  (Y1 +  S1 <= Y2) || 
                                  (Y2 +  S2 <= Y1));
                      }
                  }
              }
              break;
          }
          
          case MODEL_NOOVERLAP:{
              std::cout<<"Using the No-overlap propagator: "<<std::endl;
              IntArgs square_size(no_of_squares-1);
              for (int i = 0; i < no_of_squares-1; i++){
                  square_size[i] = size(no_of_squares, i);
              }
              NoOverlap(*this, X, square_size, Y, square_size);
              break;
          } 
      }

      /*
         * Further constrain on coordinates Y and X
         */
    for(int i = 0; i < no_of_squares-1; i++)
      {
        si = size(no_of_squares,i);
        rel(*this, ((X[i] + si) <= s));
        rel(*this, ((Y[i] + si) <= s));
      }

    /*
     * part 3: at each row and column sum of the sizes of the squares occupying space <= s.
     */

    for(int cr = 0; cr < s.max(); cr++) 
      {
        BoolVarArgs spaceAtColumn(no_of_squares-1);
        BoolVarArgs spaceAtRow(no_of_squares-1);
        for(int i = 0; i < no_of_squares-1; i++)
          {
            spaceAtColumn[i] = BoolVar(*this,0,1);      
            dom(*this, X[i], cr - size(no_of_squares,i) +1, cr, spaceAtColumn[i]);
            
            spaceAtRow[i] = BoolVar(*this,0,1);      
            dom(*this, Y[i], cr - size(no_of_squares,i) +1, cr, spaceAtRow[i]);
          }

        linear(*this, IntArgs::create(no_of_squares-1,no_of_squares,-1), spaceAtColumn, IRT_LQ, s);
        linear(*this, IntArgs::create(no_of_squares-1,no_of_squares,-1), spaceAtRow, IRT_LQ, s);
      }


    /*
     * part 4: additional constraints.
     * a) problem decomposition:
     *  already defined 
     */
    
    /*
     * part 4: additional constraints.
     * b) symmetry removal
	 * since we do not have negative interval, it is enough to say:
	 * X coordination of bigest square should be less than (size - n)/2
     */
 
    rel(*this, X[0] <= (s-no_of_squares)/2 && Y[0] <= X[0]);          
         

    /* 
     * part 4: additional constraints.
     * c)  initial domain reduction
     */

    for(int l = 0; l < no_of_squares-1; l++)
      {
          int square_size = size(no_of_squares,l);
          
          if  (square_size == 2)
          {
            rel(*this, X[l] != 1 && X[l] != 2 && Y[l] != 1 && Y[l] != 2);    
            continue;
          } else if (square_size == 3){
            rel(*this, X[l] != 2 && X[l] != 3 && Y[l] != 2 && Y[l] != 3);    
            continue;
          } else if (square_size == 4){
            rel(*this, X[l] != 2 && Y[l] != 2);
            continue;
          } else if (square_size >= 5 && square_size <= 8) {
            rel(*this, X[l] != 3 && Y[l] != 3);
            continue;
          } else if (square_size >= 9 && square_size <= 11){
            rel(*this, X[l] != 4 && Y[l] != 4);
            continue;
          } else if (square_size >= 12 && square_size <= 17){
            rel(*this, X[l] != 5 && Y[l] != 5);
            continue;
          } else if (square_size >= 18 && square_size <= 21){
            rel(*this, X[l] != 6 && Y[l] != 6);
            continue;
          } else if (square_size >= 22 && square_size <= 29){
            rel(*this, X[l] != 7 && Y[l] != 7);
            continue;
          } else if (square_size >= 30 && square_size <= 33){
            rel(*this, X[l] != 8 && Y[l] != 8);
            continue;
          } else if (square_size == 34){
            rel(*this, X[l] != 8 && Y[l] != 8);
            continue;
          } else if (square_size >= 34 && square_size <= 44){
            rel(*this, X[l] != 9 && Y[l] != 9);
            continue;
          } else if (square_size == 45){
            rel(*this, X[l] != 10 && Y[l] != 10);      
            continue;
          }
      }      
    
    /* 
     * part 4: additional constraints.
     * d)  Ignoring size 1 squares
     * 
     * As it is mentioned in given paper "we do not need to include (square 1*1) in the constraint model".
     * As can be seen we always ignore case 1*1 when updating  domains and checking interaction among squares.
     */

     /* 
      * Part 5
      */

    /*
     * (a)Branch on s first. Also we started with smallest possible value for enclosing square,
     * since we need to find out minimum value for enclosing square. 
     */
    branch(*this, s, INT_VAL_MIN()); 
    /* 
     * (b) first assign all x-coordinates, then all y-coordinates.
     * (c) To try larger squares first we used INT_VAR_NONE() since the first unassigned variable is actually the largest one 
	 *     so the assignment continues in descending order.
     * (d) To place squares from left to right we must start with minimum possible value for x-coordinates, so we used  INT_VAL_MIN
     *     and to place top to bottom we must start with maximum possible value for y-coordinates, so we used INT_VAL_MAX
     */
    branch(*this, X, INT_VAR_NONE(), INT_VAL_MIN());
    branch(*this, Y, INT_VAR_NONE(), INT_VAL_MAX());
  }

  SquarePacking(bool share, SquarePacking& sp) : Script(share,sp) {
    s.update(*this, share, sp.s);
    Y.update(*this, share, sp.Y);
    X.update(*this, share, sp.X);
    
    
  }

  virtual Space* copy(bool share) {
    return new SquarePacking(share,*this);
  }

  virtual void print(std::ostream& p) const
  {
         int ps = s.val();
      p << "The size of packing square = " << s <<std::endl;
      p << "Coordinates (starts from largest square to 2): " <<std::endl;  
      p << "X- coordinates :" << X << std::endl;
      p << "Y- coordinates:" << Y << std::endl;

    char ** matrix;

    matrix = new char * [ps];
    for (int i = 0; i < ps; i++) {
      matrix[i] = new char[ps];
      for(int j = 0; j < ps; j++) {
        matrix[i][j] = '#';
      }
    }
    for (int w = 0; w < X.size(); w++) {

      int xcord = X[w].val() + size(X.size()+1, w);
      int ycord = Y[w].val() + size(X.size()+1, w);

      for (int i = Y[w].val(); i < ycord; i++){
        for (int j = X[w].val(); j < xcord; j++){
          if(size(X.size()+1, w) > 9) matrix[i][j] = 'A' + (char)(size(X.size()+1, w) - 10);
          else matrix[i][j] = '0' + (char)size(X.size()+1, w);

        }
      }
    }
    p <<std::endl;
    for (int i = ps - 1; i >= 0; i--) {
      for (int j = 0; j < ps; j++) {
        p << matrix[i][j] << " ";
        
      }
      p << std::endl;
      
    }
  }
  
  /*
   * Static member function size that returns the size of the square with number i.
   */
  static int size(int n, int i)
  {
    return n - i;
  }
};

int main(int argc, char* argv[]) {
  SizeOptions so("Solution for square packing ");
  so.model(SquarePacking::MODEL_REIFY,"reify", "use reified constraints" );
  so.model(SquarePacking::MODEL_NOOVERLAP,"NoOverlap", "use our own no-overlap propagator" );
  so.model(SquarePacking::MODEL_NOOVERLAP);
  so.size(14);
//  so.iterations(50);
//  so.samples(100);
  //so.solutions(0);
  so.parse(argc, argv);
  
  /*
   * When using the following code line the program stops working after showing the result 
   * so we had to use statistics() method to get some statistic ;)
  */
  
//  Script::run<SquarePacking,DFS,SizeOptions>(so);
//  return 0;
//  
//  
  
  SquarePacking* sp = new SquarePacking(so);

  DFS<SquarePacking> dfs(sp);
  delete sp;
  SquarePacking* q = dfs.next();
  q->print(std::cout);
      std::cout << std::endl;
      std::cout<<"depth: "<<dfs.statistics().depth<<std::endl;
      std::cout<<"node: "<<dfs.statistics().node<<std::endl;
      std::cout<<"propagation: "<<dfs.statistics().propagate<<std::endl;
      std::cout<<"failures: "<<dfs.statistics().fail<<std::endl;
      std::cout<<"Memory: "<<dfs.statistics().memory<<std::endl;
      std::cout<<"///////////////////////"<<std::endl;
      delete q;
  

  return 0;
}

