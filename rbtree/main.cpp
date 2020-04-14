//
// Created by Lie Yan on 2020/4/11.
//

#include "rbtree.h"
#include <iostream>
#include <vector>

int main () {

  auto* p = new RBTree();

  for (int i = 0; i < 20; i++) {
    int x = std::rand() % 30 + 100;
    p->insert(x, x);
  }

  std::cout << p->least()->key << std::endl;
  std::cout << p->greatest()->key << std::endl;

  for (auto t = p->successor(nullptr); t != nullptr; t = p->successor(t)) {
    std::cout << t->key << " " << t->value << std::endl;
  }
}
