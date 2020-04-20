//
// Created by Lie Yan on 2020/4/11.
//

#include "rbtree.h"
#include <iostream>
#include <vector>
#include <random>
#include <thread>

void print_sequence (const RBTree& p) {
  for (auto t = p.successor(nullptr); t != nullptr; t = p.successor(t)) {
    std::cout << t->key << " ";
  }
}

void print_tree (const RBTree& p) {
  std::cout << p.string_rep() << std::endl;
}

void print_vector (const std::vector<int>& v) {
  for (auto x: v) {
    printf("%d, ", x);
  }
  printf("\n");
}

void test () {
  auto p = std::make_unique<RBTree>();
  std::random_device              rd;
  std::mt19937                    g(rd());
  std::uniform_int_distribution<> dist1(1, 30);
  std::uniform_int_distribution<> dist2(1, 8000);

  std::vector<int> v;

  int count = dist1(g);
  v.clear();
  for (int i = 0; i < count; ++i) {
    v.push_back(dist2(g));
  }

  std::sort(v.begin(), v.end());
  auto last = std::unique(v.begin(), v.end());
  v.erase(last, v.end());
  std::shuffle(v.begin(), v.end(), g);
  print_vector(v);

  for (auto x: v) {
    printf("x = %2d: ", x);
    p->insert(x, 0);
    print_sequence(*p);
    std::cout << "\n";
  }

  //  std::cout << p->lower_bound(6)->key << std::endl;
  //  std::cout << p->lower_bound(7)->key << std::endl;
  std::cout << p->min()->key << std::endl;
  std::cout << p->max()->key << std::endl;

  print_sequence(*p);
  std::cout << "\n";

  std::shuffle(v.begin(), v.end(), g);

  //  v = {3, 10, 7, 1, 4, 9, 6, 8, 2, 5,};
  print_vector(v);
  for (auto x: v) {
    printf("x = %2d: ", x);
    p->erase(x);
    print_sequence(*p);
    std::cout << "\n";
  }
}

int main () {
  using namespace std::chrono_literals;

  while (true) {
    printf("===================\n");
    test();
    std::this_thread::sleep_for(1ms);
  }
}
