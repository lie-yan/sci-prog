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
   *  The result depends on the position of the node in the node sequence.
   *    1) If it is the initial node, return null.
   *    2) Otherwise, return its predecessor.
   *    3) In the case of null node, return the final node of the node sequence.
   */
  Node* predecessor(Node* t) const {
    if (t == nullptr) return rightmost(root);

    // t != nullptr
    if (t->left != nullptr) { // has left subtree
      return rightmost(t->left);
    } else if (t->p == nullptr) { // no left subtree ∧ no parent
      // no left subtree ∧ no parent ⇒ initial node
      return nullptr;
    } else if (t->p->right == t) { // no left subtree ∧ be right child
      return t->p;
    } else { // no left subtree ∧ be left child
      // no left subtree ∧ be left child ⇒ predecessor(t) = predecessor(t->p)
      return predecessor(t->p);
    }
  }
  
  /**
   *  Given a node in the search tree, return its successor node. 
   *  
   *  The result depends on the position of the node in the node sequence.
   *    1) If it is the final node, return null.
   *    2) Otherwise, return its successor.
   *    3) In the case of null node, return the initial node of the node sequence.
   */
  Node* successor(Node* t) const;

  /**
   *  Given a node t, return the leftmost node in the subtree rooted at t.
   *  In the case of a null node, return null.
   */
  Node* leftmost(Node* t) const {
    if (t == nullptr) return nullptr;

    // t != nullptr
    auto[p, q] = std::tie(t, t->left);
    while (q != nullptr) {
      std::tie(p, q) = std::tie(q, q->left);
    }
    return p;
  }

  /**
   *  Given a node t, return the rightmost node in the subtree rooted at t.
   *  In the case of a null node, return null.
   */
  Node* rightmost(Node* t) const {
    if (t == nullptr) return nullptr;

    // t != nullptr
    auto[p, q] = std::tie(t, t->right);
    while (q != nullptr) {
      std::tie(p, q) = std::tie(q, q->right);
    }
    return p;
  }

private:
  Node* root;
};