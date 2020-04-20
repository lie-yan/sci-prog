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

void print_vector (const std::vector<std::pair<int, int>>& v) {
  for (auto x: v) {
    printf("{%d,%d}, ", x.first, x.second);
  }
  printf("\n");
}

std::vector<std::pair<int, int>> random_update_sequence (int max_count, int max_value) {
  std::random_device              rd;
  std::mt19937                    g(rd());
  std::uniform_int_distribution<> dist1(1, max_count);
  std::uniform_int_distribution<> dist2(1, max_value);

  std::vector<std::pair<std::pair<int, int>, int>> v;

  int count = dist1(g);
  v.clear();
  for (int i = 0; i < count; ++i) {
    int x = dist2(g);
    v.emplace_back(std::pair{x, 0}, 0);
    v.emplace_back(std::pair{x, 1}, 0);
  }

  std::sort(v.begin(), v.end());
  auto last = std::unique(v.begin(), v.end());
  v.erase(last, v.end());

  for (int i = 0; i < count; ++i) {
    int m = dist2(g);
    int n = dist2(g);

    if (m == n) n++;
    if (m > n) std::swap(m, n);
    assert(m < n);

    v[2 * i].second     = m;
    v[2 * i + 1].second = n;
  }

  std::sort(v.begin(), v.end(), [] (const auto& x, const auto& y) {
    return x.second < y.second;
  });

  std::vector<std::pair<int, int>> res;

  std::transform(v.begin(), v.end(), std::back_inserter(res),
                 [] (const auto& x) {
                   return x.first;
                 });
  return res;
}

void test () {
  auto v = random_update_sequence(100, 800);

  auto p = std::make_unique<RBTree>();

  for (const auto& x : v) {
    if (x.second == 0) p->insert(x.first, 0);
    else p->erase(x.first);

//    print_sequence(*p);

    print_tree(*p);
    printf("\n");
  }
}

int main () {
  using namespace std::chrono_literals;

//  while (true) {
    printf("===================\n");
    test();
    std::this_thread::sleep_for(1ms);
//  }
}
