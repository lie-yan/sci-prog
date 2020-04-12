#include <iostream>
#include <vector>


/**
 *  Given a base b, an exponent e, return b^e.
 */
int powi(int b, int e) {
  // e0 := e
  
  int acc = 1;
  int p = b;

  // Invariant:
  //    b^e0 = acc * p^e
  // Note:
  //    If e = 2m+1, then acc * p^e = acc * p^(2m+1) = (acc * p) * (p^2)^m.
  //    If e = 2m, then acc * p^e = acc * p^(2m) = acc * (p^2)^m.
  while (e > 0) {
    if (e % 2) acc *= p;
    p *= p;
    e /= 2;
  }
  
  // acc = b^e0
  return acc;
}


/**
 *  Given an integer x, a window size ell, return the decomposition of 
 *  x under windowing scheme. 
 */
std::vector<int> decompose_integer_windowing(int x, int ell) {
  
  return {};
}


int main() {
  std::cout << powi(3, 0) << std::endl;
  std::cout << powi(3, 1) << std::endl;
  std::cout << powi(3, 2) << std::endl;
  std::cout << powi(3, 3) << std::endl;
  std::cout << powi(3, 4) << std::endl;
  std::cout << powi(3, 5) << std::endl;

  std::cout << powi(2, 0) << std::endl;
  std::cout << powi(2, 1) << std::endl;
  std::cout << powi(2, 2) << std::endl;
  std::cout << powi(2, 3) << std::endl;
  std::cout << powi(2, 4) << std::endl;
  std::cout << powi(2, 5) << std::endl;

  
  std::cout << "hello\n";
}
