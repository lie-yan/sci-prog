#include <iostream>
#include <vector>

/**
 *  Given a vector v, an index range [begin, end), and an integer pivot, 
 *  rearrange v's elements in index range [begin, end) in place 
 *  into two consecutive parts so that all the elements in the 
 *  first part are less than pivot, and the second greater than 
 *  or equal to pivot. The return value is the index of the start 
 *  of the second part.
 */
int partition(std::vector<int>& v, int begin, int end, int pivot) {
  int i = begin; 
  int j = end;

  // Let P(i) be ∀k∈[begin, i): v[k] < pivot.
  // Let Q(j) be ∀k∈[j, end): v[k] >= pivot.
  // Invariant: P(i) ∧ Q(j)
  while (i < j) {
    if (v[i] >= pivot) std::swap(v[i], v[--j]);
    else i++;
  }
  
  // i = j ∧ P(i) ∧ Q(j)
  // Note: P(i)∧Q(j) ⇒ ¬Q(j-1)∧Q(j)
  return j;
}

/**
 *  Given a vector v, and an index range [begin, end), rearrange
 *  v's elements in index range [begin, end) so that they are in
 *  non-decreasing order.
 */
void qsort(std::vector<int>& v, int begin, int end) {
  int n = end - begin;  
  if (n <= 1) return;
  // n > 1
      
  int p = begin + std::rand() % n;
  // begin <= p < end
  // pivot := v[p]
  
  int stash = end - 1;
  std::swap(v[stash], v[p]);
  
  int q = partition(v, begin, stash, v[stash]);
  // ∀i∈[begin, q): v[i] < pivot
  // ∀i∈[q, stash): v[i] >= pivot
  
  std::swap(v[q], v[stash]);
  // v[q] = pivot
  qsort(v, begin, q);
  qsort(v, q+1, end);
  // (q - begin < n)∧(end - (q+1) < n) ⇒ termination
}

std::vector<int> sort_and_print(std::vector<int> v) {
  
  auto print_vector = [](const auto& v) {
    for (const auto& x: v) {
      std::cout << x << " ";
    }
  };

  std::cout << "Before: ";
  print_vector(v);
  std::cout << "\n";
  
  qsort(v, 0, v.size());

  std::cout << " After: ";
  print_vector(v);
  std::cout << "\n";
  
  return v;
}

int main() {
  sort_and_print({3,11,21,13,6});
  sort_and_print({1, 1, 1, 1, 1});
}
