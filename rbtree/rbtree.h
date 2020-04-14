//
// Created by Lie Yan on 2020/4/11.
//

#pragma once

#include <cstdint>
#include <optional>
#include <iostream>

class RBTree {
public:
  using K = int;
  using V = int;
  using T = std::pair<K, V>;

  enum class Color : uint8_t {
    BLACK = 0,
    RED,
  };

  struct Node {
    Color color;
    Node* p     = nullptr;
    Node* left  = nullptr;
    Node* right = nullptr;

    K key;
    V value;

    Node (K key, V value, Color color)
        : key(key), value(value), color(color) { }
  };

  [[nodiscard]] Node* root () const { return root_; }

  /**
   * @brief Given a key and a value, insert (key, value) into the search tree.
   */
  void insert (K key, V value) {
    root_ = insert(root_, key, value);
    root_->p     = nullptr;
    root_->color = Color::BLACK;
  }

  static Node* insert (Node* t, K key, V value) {
    if (t == nullptr)
      return new Node(key, value, Color::RED);

    // t != nullptr

    if (key < t->key) {
      t->left    = insert(t->left, key, value);
      t->left->p = t;
    } else if (t->key < key) {
      t->right    = insert(t->right, key, value);
      t->right->p = t;
    } else {
      t->value = value;
    }

    if (is_red(t->right) && !is_red(t->left)) {
      // t->right != nullptr
      auto p = t->p;
      t = rotate_left(t);
      t->p = p;
    }
    if (is_red(t->left) && is_red(t->left->left)) {
      // t->left && t->left->left
      auto p = t->p;
      t = rotate_right(t);
      t->p = p;
    }
    if (is_red(t->left) && is_red(t->right)) {
      // t->left && t->right
      flip_colors(t);
    }

    return t;
  }

  void erase (K key) {

  }

  /**
   * @brief Given a node in the search tree, return its predecessor node.
   *
   *  The return value depends on the position of the node in the represented
   *  sequence.
   *    1) If it is the initial node, return null.
   *    2) Otherwise, return its predecessor.
   *    3) In the case of null node, return the final node of the represented
   *       sequence.
   */
  Node* predecessor (Node* t) const {
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
   * @brief Given a node in the search tree, return its successor node.
   *
   *  The return value depends on the position of the node in the represented
   *  sequence.
   *    1) If it is the final node, return null.
   *    2) Otherwise, return its successor.
   *    3) In the case of null node, return the initial node of the represented
   *       sequence.
   */
  Node* successor (Node* t) const {
    if (t == nullptr) {
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

  [[nodiscard]] Node* least () const { return leftmost(root_); }

  [[nodiscard]] Node* greatest () const { return rightmost(root_); }

protected:
  /**
   * @brief Given a node t, return whether the link pointing to its parent
   *  is red.
   *
   * @note  is_red(t) ⇒ (t != nullptr)
   */
  static bool is_red (Node* t) {
    if (t == nullptr) return false;
    else return t->color == Color::RED;
  }

  /**
   * @brief Given a node t, left rotate around t and return the new root.
   *
   *  The parent links below the new root are well set. The parent link of the
   *  new root is not.
   *
   * @pre t && t->right
   */
  static Node* rotate_left (Node* t) {
    assert(t && t->right);

    auto x = t->right;
    // x != nullptr
    std::tie(t->right, x->left)  = std::pair(x->left, t);
    std::tie(x->color, t->color) = std::pair(t->color, Color::RED);

    if (t->right) t->right->p = t;
    t->p = x;

    return x;
  }

  /**
   * @brief Given a node t, right rotate around t and return the new root.
   *
   *  The parent links below the new root are well set. The parent link of the
   *  new root is not.
   *
   * @pre t && t->left && t->left->left
   */
  static Node* rotate_right (Node* t) {
    assert(t && t->left && t->left->left);

    auto x = t->left;
    // x != nullptr
    std::tie(t->left, x->right)  = std::pair(x->right, t);
    std::tie(x->color, t->color) = std::pair(t->color, Color::RED);

    if (t->left) t->left->p = t;
    t->p = x;

    return x;
  }

  /**
   * @brief Given a node t, flip the colors of itself and its two children.
   */
  static void flip_colors (Node* t) {
    assert(t && t->color == Color::BLACK);

    t->color        = Color::RED;
    t->left->color  = Color::BLACK;
    t->right->color = Color::BLACK;
  }

  /**
   * @brief Given a node t, return the leftmost node in the subtree rooted at t.
   *
   *  In the case of null node, return null.
   */
  static Node* leftmost (Node* t) {
    if (t == nullptr) return nullptr;

    // t != nullptr
    auto[p, q] = std::pair(t, t->left);
    while (q != nullptr) {
      std::tie(p, q) = std::pair(q, q->left);
    }
    return p;
  }

  /**
   * @brief Given a node t, return the rightmost node in the subtree rooted at t.
   *
   *  In the case of null node, return null.
   */
  static Node* rightmost (Node* t) {
    if (t == nullptr) return nullptr;

    // t != nullptr
    auto[p, q] = std::pair(t, t->right);
    while (q != nullptr) {
      std::tie(p, q) = std::pair(q, q->right);
    }
    return p;
  }

  /**
   * @brief Given a node t, return a pair (u, v) such that u is obtained by
   *  repeatedly following the edge to parent, starting from t, as long as the
   *  source is a left child.
   *
   *  The value of node v is
   *    1) the parent of u, if u is the right child of its parent;
   *    2) null, otherwise.
   *
   * @pre t != nullptr
   * @post (v == nullptr) ∨ (v != nullptr ∧ u == v->right)
   */
  static std::tuple<Node*, Node*> ascend_rightward (Node* t) {
    assert(t != nullptr);

    auto[u, v] = std::pair(t, t->p);
    while (v != nullptr && u == v->left) {
      std::tie(u, v) = std::pair(v, v->p);
    }
    // (v == nullptr) ∨ (v != nullptr ∧ u == v->right)
    return {u, v};
  }

  /**
   * @brief Given a node t, return a pair (u, v) such that u is obtained by
   *  repeatedly following the edge to parent, starting from t, as long as the
   *  source is a right child.
   *
   *  The value of node v is
   *    1) the parent of u, if u is the left child of its parent;
   *    2) null, otherwise.
   *
   *  @pre: t != nullptr
   *  @post: (v == nullptr) ∨ (v != nullptr ∧ u == v->left)
   */
  static std::tuple<Node*, Node*> ascend_leftward (Node* t) {
    assert(t != nullptr);

    auto[u, v] = std::pair(t, t->p);
    while (v != nullptr && u == v->right) {
      std::tie(u, v) = std::pair(v, v->p);
    }
    // (v == nullptr) ∨ (v != nullptr ∧ u == v->left)
    return {u, v};
  }

private:
  Node* root_;
  int size_;
};
