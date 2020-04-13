//
// Created by Lie Yan on 2020/4/11.
//

#pragma once

#include <cstdint>
#include <optional>


class RBTree {
public:
  using K = int;
  using V = int;
  using T = std::pair<K, V>;

  enum {
    BLACK = 0,
    RED,
  };

  std::optional<T> find(K key) const;
  void insert(K key, V value);
  void erase(K key);

protected:
  struct Node {
    uint8_t color;
    Node *p;
    Node *left;
    Node *right;

    T payload;
  };

private:
  Node* root;
};