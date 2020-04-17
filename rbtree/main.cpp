//
// Created by Lie Yan on 2020/4/11.
//

#include "rbtree.h"
#include <iostream>
#include <vector>

int main () {

  auto* p = new RBTree();

  std::vector<int> v = {1, 3, 5, 7, 9};
  for (auto        x: v) {
    p->insert(x, 0);
  }

  std::cout << p->lower_bound(6)->key << std::endl;
  std::cout << p->lower_bound(7)->key << std::endl;
  std::cout << p->least()->key << std::endl;
  std::cout << p->greatest()->key << std::endl;

  for (auto t = p->successor(nullptr); t != nullptr; t = p->successor(t)) {
    std::cout << t->key << " " << t->value << std::endl;
  }
}
