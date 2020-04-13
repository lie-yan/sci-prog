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

protected:
  struct Node {
    uint8_t color;
    Node *p;
    Node *left;
    Node *right;

    T payload;
  };

public:
  std::optional<T> find(K key) const;
  void insert(K key, V value);
  void erase(K key);

protected:
  /**
   *  Given a node in the search tree, return its predecessor node. 
   *  
   *  The rule is as follows.
   *    1) If the node is null, return null.
   *    2) Or, return its predeceessor if any.
   *    3) Otherwise return null.
   */
  Node* predecessor(Node* t) const {
    if (t == nullptr) return nullptr;

    // t != nullptr

    
  }
  
  /**
   *  Given a node in the search tree, return its successor node. 
   *  
   *  The rule is as follows.
   *    1) If the node is null, return null.
   *    2) Or, return its successor if any.
   *    3) Otherwise return null.
   */
  Node* successor(Node* t) const;

private:
  Node* root;
};