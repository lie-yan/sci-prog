//
// Created by Lie Yan on 2020/4/11.
//

#include "rbtree.h"
#include <iostream>
#include <vector>

void print_sequence (RBTree* p) {
  for (auto t = p->successor(nullptr); t != nullptr; t = p->successor(t)) {
    std::cout << t->key << " ";
  }
}

int main () {

  auto* p = new RBTree();

  std::vector<int> v = {5, 7, 9, 1, 3, 11};

  for (auto        x: v) {
//  int count = 20;
//  for  (int i = 0; i < count; i++) {
//    int x = std::rand() % count;
    printf("x = %2d: ", x);
    p->insert(x, 0);
    print_sequence(p);
    std::cout << "\n";
  }


  std::cout << p->lower_bound(6)->key << std::endl;
  std::cout << p->lower_bound(7)->key << std::endl;
  std::cout << p->least()->key << std::endl;
  std::cout << p->greatest()->key << std::endl;

  print_sequence(p);
  std::cout << "\n";

}
