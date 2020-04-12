#include <iostream>
#include <vector>
#include <cassert>


/**
 *  Given a base b, an exponent e, return b^e.
 *  Pre: b > 0, e >= 0. 
 */
int powi(int b, int e) {
  assert(b > 0 && e >= 0);

  // e0 := e  
  int acc = 1;
  int p = b;

  // Invariant:
  //    b^e0 = acc * p^e
  // Note:
  //    If e = 2m+1, then acc * p^e = acc * p^(2m+1) = (acc*p) * (p^2)^m.
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
 *  Given a base b, an exponent e, return b^(2^e).
 *  Pre: b > 0, e >= 0. 
 */
int powi_tower2(int b, int e) {
  assert (b > 0 && e >= 0);

  int acc = b;
  // int d = 0;

  // e0 := e
  // Invariant: acc = b^(2^d) ∧ b^(2^e0) = b^(2^(d+e)) ∧ e0 = d + e
  while (e > 0) {
    acc *= acc;
    // d += 1;
    e -= 1;
  }

  // acc = b^(2^e0)
  return acc;
}

/**
 *  Given a base b, an integer x, return an integer e such that b^e <= x and b^(e+1) > x.
 *  In other words, e = ⌊log_b x⌋. 
 *  Pre: b > 1, x > 0
 */
int logi(int b, int x) {
  assert(b > 1 && x > 0);

  int pow = 1;
  int acc = 0;

  // Invariant: 
  //    pow = b^acc
  //    b^(acc + y) <= x
  //    b^(acc + y + 1) > x
  //    y > 0
  // Counter: y
  while (pow * b <= x) {

    int k = 1;
    while (pow * powi_tower2(b, k) <= x) ++k;
    --k;
    // k>=0 ∧ k = ARGMAX (pow * b^(2^k) <= x)

    pow *= powi_tower2(b, k);
    acc += powi(2, k);
  }

  return acc;
}

/**
 *  Given a positive integer x, a window size ell, return a pair (i,j) sucht that
 *    1) 1 <= i <= 2^ell - 1,
 *    2) j >= 0,
 *    3) i * 2^(ell*j) <= x,
 *    4) (i+1) * 2^(ell*j) > x,
 *    5) i * 2^(ell*(j+1)) > x.
 *  The above conditions imply (2^ell)^j <= x ∧ (2^ell)^(j+1) > x.
 */
std::tuple<int, int> solve_for_windowing(int x, int ell) {
  assert(x > 0 && ell > 0);

  int b = powi(2, ell);
  int j = logi(b, x);
  int i = x / powi(b, j);
  return {i, j};
}

/**
 *  Given a nonnegative integer x, a window size ell, return the representation of x
 *  under windowing scheme.
 */
std::vector<std::tuple<int, int>> windowing_decompose(int x, int ell) {
  assert(x > 0 && ell > 0);

  std::vector<std::tuple<int, int>> ret;  
  while (x > 0) {
    auto[i, j] = solve_for_windowing(x, ell);
    ret.emplace_back(i, j);
    x -= i * powi(2, j*ell);
  }
  return ret;
}


int main() {
  std::cout << powi(3, 0) << std::endl;
  std::cout << powi(3, 1) << std::endl;
  std::cout << powi(3, 2) << std::endl;
  std::cout << powi(3, 3) << std::endl;
  std::cout << powi(3, 4) << std::endl;
  std::cout << powi(3, 5) << std::endl;

  std::cout << logi(3, 241) << std::endl;
  std::cout << logi(3, 243) << std::endl;

  auto coord = solve_for_windowing(100, 2);
  std::cout << std::get<0>(coord) << ", " << std::get<1>(coord) << std::endl;

  auto v = windowing_decompose(100, 2);
  for (const auto& coord : v) {
    std::cout << std::get<0>(coord) << ", " << std::get<1>(coord) << std::endl;
  }
}
