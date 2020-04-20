//
// Created by Lie Yan on 2020/4/11.
//

#include "rbtree.h"
#include <iostream>
#include <vector>
#include <random>

void print_sequence (const RBTree& p) {
  for (auto t = p.successor(nullptr); t != nullptr; t = p.successor(t)) {
    std::cout << t->key << " ";
  }
}

void print_vector (const std::vector<int>& v) {
  for (auto x: v) {
    printf("%d, ", x);
  }
  printf("\n");
}

void test () {

  auto p = std::make_unique<RBTree>();

  std::random_device rd;
  std::mt19937       g(rd());

  std::vector<int> v = {3, 1, 11, 9, 7, 5,};

  std::shuffle(v.begin(), v.end(), g);
  print_vector(v);

  for (auto x: v) {
    printf("x = %2d: ", x);
    p->insert(x, 0);
    print_sequence(*p);
    std::cout << "\n";
  }

  std::cout << p->lower_bound(6)->key << std::endl;
  std::cout << p->lower_bound(7)->key << std::endl;
  std::cout << p->least()->key << std::endl;
  std::cout << p->greatest()->key << std::endl;

  print_sequence(*p);
  std::cout << "\n";

  std::shuffle(v.begin(), v.end(), g);


//  v = {1, 7, 9, 11, 3, 5, };
  print_vector(v);
  for (auto x: v) {
    printf("x = %2d: ", x);
    p->erase(x);
    print_sequence(*p);
    std::cout << "\n";
  }
}

int main () {

  for (int i = 0; i < 1000; i++) {
    printf("========= %d ==========\n", i);
    test();
  }
}
