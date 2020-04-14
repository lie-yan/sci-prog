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
   *  The result depends on the position of the node in the represented sequence.
   *    1) If it is the initial node, return null.
   *    2) Otherwise, return its predecessor.
   *    3) In the case of null node, return the final node of the represented 
   *       sequence.
   */
  Node* predecessor(Node* t) const {
    if (t == nullptr) {
      return rightmost(root_);
    } else if (t->left != nullptr) { // has left subtree
      return rightmost(t->left);
    } else if (t->p == nullptr) { // no left subtree ∧ be root
      // no left subtree ∧ be root ⇒ initial node
      return nullptr;
    } else if (t->p->right == t) { // no left subtree ∧ be right child
      return t->p;
    } else { // no left subtree ∧ be left child
      // t->p != nullptr
      auto[u, v] = ascend_rightward(t->p);
      // (v == nullptr) ∨ (v != nullptr ∧ u == v->right)
      return v;
    }
  }
  
  /**
   *  Given a node in the search tree, return its successor node. 
   *  
   *  The result depends on the position of the node in the represented sequence.
   *    1) If it is the final node, return null.
   *    2) Otherwise, return its successor.
   *    3) In the case of null node, return the initial node of the 
   *       represented sequence.
   */
  Node* successor(Node* t) const {
    if (t==nullptr) {
      return leftmost(root_);
    } else if (t->right != nullptr) { // has right subtree
      return leftmost(t->right);
    } else if (t->p == nullptr) { // no right subtree ∧ be root
      // no right subtree ∧ be root ⇒ final node
      return nullptr;
    } else if (t->p->left == t) { // no right subtree ∧ be left child
      return t->p;
    } else { // no right subtree ∧ be right child

      // t->p != nullptr
      auto[u, v] = ascend_leftward(t->p);
      // (v == nullptr) ∨ (v != nullptr ∧ u == v->left)
      return v;
    }
  }

  /**
   *  Given a node t, return the leftmost node in the subtree rooted at t.
   *  In the case of a null node, return null.
   */
  static Node* leftmost(Node* t) {
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
  static Node* rightmost(Node* t) {
    if (t == nullptr) return nullptr;

    // t != nullptr
    auto[p, q] = std::tie(t, t->right);
    while (q != nullptr) {
      std::tie(p, q) = std::tie(q, q->right);
    }
    return p;
  }

  /**
   *  Given a node t, return a pair (u, v) such that u is obtained by 
   *  repeatedly following the edge to parent, starting from t, as long
   *  as the source is a left child.
   *  
   *  The value of node v is
   *    1) the parent of u, if u is the right child of its parent;
   *    2) null, otherwise.
   *  
   *  Pre: t != nullptr
   *  Post: (v == nullptr) ∨ (v != nullptr ∧ u == v->right)
   */
  static std::tuple<Node*, Node*> ascend_rightward(Node* t) {
    assert(t != nullptr);

    auto[u, v] = std::tie(t, t->p);
    while (v != nullptr && u == v->left) {
      std::tie(u, v) = std::tie(v, v->p);
    }
    // (v == nullptr) ∨ (v != nullptr ∧ u == v->right)
    return {u, v};
  }


  /**
   *  Given a node t, return a pair (u, v) such that u is obtained by 
   *  repeatedly following the edge to parent, starting from t, as long
   *  as the source is a right child.
   *  
   *  The value of node v is
   *    1) the parent of u, if u is the left child of its parent;
   *    2) null, otherwise.
   *  
   *  Pre: t != nullptr
   *  Post: (v == nullptr) ∨ (v != nullptr ∧ u == v->left)
   */
  static std::tuple<Node*, Node*> ascend_leftward(Node* t) {
    assert(t != nullptr);

    auto[u, v] = std::tie(t, t->p);
    while (v != nullptr && u == v->right) {
      std::tie(u, v) = std::tie(v, v->p);
    }
    // (v == nullptr) ∨ (v != nullptr ∧ u == v->left)
    return {u, v};
  }

private:
  Node* root_;
  int size_;
};
