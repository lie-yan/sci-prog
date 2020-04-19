//
// Created by Lie Yan on 2020/4/11.
//

#pragma once

#define DEBUG 1

#include <cstdint>
#include <optional>
#include <iostream>
#include <tuple>

template <typename T>
class scoped_ptr : public std::unique_ptr<T> {
public:
#pragma clang diagnostic push
#pragma ide diagnostic ignored "google-explicit-constructor"

  scoped_ptr (T* p = 0) : std::unique_ptr<T>(p) { }

#pragma clang diagnostic pop
};

/**
 * @brief A red-black tree.
 *
 * @invariant
 *    Tarjan invariant:
 *    1) If x is any node with a parent, rank(x) ≤ rank(p(x)) ≤ rank(x) + 1.
 *    2) If x is any node with a grandparent, rank(x) < rank(p(p(x))).
 *    3) If x is an external node, rank(x) = 0 and rank(p(x)) = 1 if x has
 *       a parent.
 *    Refer to Data Structures and Network Algorithms by Tarjan.
 *
 * @invariant
 *    Sedgewick invariant:
 *    1) Symmetric order.
 *    2) Red links lean left.
 *    3) No node has two red links connected to it.
 *    4) Perfect black balance: every path from an internal node to a null link
 *       has the same number of black links.
 *    Refer to Algorithms by Sedgewick and Wayne.
 */
class RBTree {
public:
  using Key = int;
  using Value = int;

  enum class Color : uint8_t {
    BLACK = 0,
    RED,
  };

  struct Node {
    Color color;
    Node* parent = nullptr;
    Node* left   = nullptr;
    Node* right  = nullptr;

    Key   key;
    Value value;

    Node (Key key, Value value, Color color)
        : key(key), value(value), color(color) { }
  };

  [[nodiscard]] bool is_empty () const { return nullptr == root_; }

  [[nodiscard]] Node* least () const { return leftmost(root_); }

  [[nodiscard]] Node* greatest () const { return rightmost(root_); }

  /**
   * @brief Given a key, return the node corresponding to the greatest key less
   *    than or equal to the given key.
   *
   *    If no such node exists, return null.
   */
  [[nodiscard]] Node* lower_bound (const Key& key) const {
    auto[u, p]= std::pair((Node*)nullptr, root_);
    // Let P be the set of nodes that have been compared with the given key.
    // Let P' be { x ∈ P | x.key ≤ key }.
    // Invariant:
    //    Q(u): u is the node in P' with the maximum key.
    while (p) {
      if (key < p->key)
        p = p->left;
      else if (p->key < key)
        u = p, p = p->right;
      else
        u = p, p = nullptr;
    }

    // Property:
    //    The least element no less than key, and the greatest element no
    //    greater than key must be in P.
    return u;
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
    } else if (t->parent == nullptr) { // no left subtree ∧ be root
      // no left subtree ∧ be root ⇒ initial node
      return nullptr;
    } else if (t->parent->right == t) { // no left subtree ∧ be right child
      return t->parent;
    } else { // no left subtree ∧ be left child
      // t->parent != nullptr
      auto[u, v] = ascend_rightward(t->parent);
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
    } else if (t->parent == nullptr) { // no right subtree ∧ be root
      // no right subtree ∧ be root ⇒ final node
      return nullptr;
    } else if (t->parent->left == t) { // no right subtree ∧ be left child
      return t->parent;
    } else { // no right subtree ∧ be right child

      // t->parent != nullptr
      auto[u, v] = ascend_leftward(t->parent);
      // (v == nullptr) ∨ (v != nullptr ∧ u == v->left)
      return v;
    }
  }

  /**
   * @brief Given a key and a value, insert (key, value) into the search tree.
   *
   *    If key already exists in the search tree, replace the value.
   */
  void insert (Key key, Value value) {
    root_ = tarjan_insert(root_, key, value);
    root_->parent = nullptr;
    root_->color  = Color::BLACK;
  }

  void erase (Key key) {

  }

protected:
  static Node* Parent (Node* x) {
    if (x) return x->parent;
    else return nullptr;
  }

  static Node* Grandparent (Node* x) {
    return Parent(Parent(x));
  }

  static Node* Sibling (Node* x) {
    if (nullptr == x) return nullptr;
    else if (nullptr == x->parent) return nullptr;
    else if (x == x->parent->left) return x->parent->right;
    else return x->parent->left;
  }

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
   * @brief Given a node t and a key, return a pair (p, tp) such that p is the
   *    node with the given key under the subtree rooted at t, and tp (for
   *    "trailing pointer") is the parent of t.
   *
   *    If p is the root, return (p, null).
   *    If no such p is found, return (null, tp0) where tp0 is the last node
   *    checked before return.
   *
   */
  static std::tuple<Node*, Node*> find (Node* t, const Key& key) {
    auto[p, tp]= std::pair(t, (Node*)nullptr);
    while (p) {
      if (key < p->key)
        tp = p, p = p->left;
      else if (p->key < key)
        tp = p, p = p->right;
      else
        break;
    }
    return {p, tp};
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
      p = q, q = q->left;
    }
    return p;
  }

  /**
   * @brief Given a node t, return the rightmost node in the subtree rooted
   *  at t.
   *
   *  In the case of null node, return null.
   */
  static Node* rightmost (Node* t) {
    if (t == nullptr) return nullptr;

    // t != nullptr
    auto[p, q] = std::pair(t, t->right);
    while (q != nullptr) {
      p = q, q = q->right;
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

    auto[u, v] = std::pair(t, t->parent);
    while (v != nullptr && u == v->left) {
      u = v, v = v->parent;
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
   * @pre   t != nullptr
   * @post  (v == nullptr) ∨ (v != nullptr ∧ u == v->left)
   */
  static std::tuple<Node*, Node*> ascend_leftward (Node* t) {
    assert(t != nullptr);

    auto[u, v] = std::pair(t, t->parent);
    while (v != nullptr && u == v->right) {
      u = v, v = v->parent;
    }
    // (v == nullptr) ∨ (v != nullptr ∧ u == v->left)
    return {u, v};
  }

  /**
   * @brief Repair the parent link of t so that it points to p.
   */
  static void repair_parent_link (Node* t, Node* p) {
    if (t) t->parent = p;
  }

  /**
   * @brief Given a node t, left rotate around t and return the new root.
   *
   *  The parent links below the new root are well set. The parent link of the
   *  new root is not.
   *
   * @pre t && t->right
   * @invariant rotate_left() preserves invariant 1) and 4).
   */
  static Node* rotate_left (Node* t) {
    assert(t && t->right);

    auto x = t->right;
    // x != nullptr
    t->right = x->left, x->left = t;
    x->color = t->color, t->color  = Color::RED;
    if (t->right) t->right->parent = t;
    t->parent = x;

    return x;
  }

  /**
   * @brief Given a node t, right rotate around t and return the new root.
   *
   *  The parent links below the new root are well set. The parent link of the
   *  new root is not.
   *
   * @pre t && t->left
   * @invariant rotate_right() preserves invariant 1) and 4).
   */
  static Node* rotate_right (Node* t) {
    assert(t && t->left);

    auto x = t->left;
    // x != nullptr
    t->left = x->right, x->right = t;
    x->color = t->color, t->color = Color::RED;

    if (t->left) t->left->parent = t;
    t->parent = x;

    return x;
  }

  /**
   * @brief Given a node t, flip the colors of itself and its two children.
   */
  static void flip_colors (Node* t) {
    auto flip = [] (Color c) -> Color {
      switch (c) {
      case Color::BLACK:
        return Color::RED;
      case Color::RED:
        return Color::BLACK;
      }
    };

    t->color        = flip(t->color);
    t->left->color  = flip(t->left->color);
    t->right->color = flip(t->right->color);
  }

  /**
   * @post The new root is hung under the old parent of t.
   */
  static Node* sedgewick_insert (Node* t, Key key, Value value) {
    if (t == nullptr)
      return new Node(key, value, Color::RED);

    // t != nullptr

    if (key < t->key) {
      t->left = sedgewick_insert(t->left, key, value);
      repair_parent_link(t->left, t);
    } else if (t->key < key) {
      t->right = sedgewick_insert(t->right, key, value);
      repair_parent_link(t->right, t);
    } else {
      t->value = value;
    }

    if (is_red(t->right) && !is_red(t->left)) { // right leaning red link
      // t->right != nullptr
      auto tmp = t->parent;
      t = rotate_left(t);
      repair_parent_link(t, tmp);
    }
    if (is_red(t->left) && is_red(t->left->left)) {
      // t->left && t->left->left
      auto tmp = t->parent;
      t        = rotate_right(t);
      repair_parent_link(t, tmp);
    }
    if (is_red(t->left) && is_red(t->right)) {
      // t->left && t->right
      flip_colors(t);
    }

    return t;
  }

  /**
   * @post The new root is hung under the old parent of t.
   */
  static Node* tarjan_insert (Node* t, Key key, Value value) {

    auto[found, tp] = find(t, key);

    // Cases:
    //  1) found
    //  2) empty tree
    //  3) nonempty tree and not found

    if (found) { // Case 1)
      found->value = value;
      return t;
    } else if (nullptr == tp) { // Case 2)
      assert(nullptr == t);
      return new Node(key, value, Color::RED);
    }

    // Case 3)

    auto* x = new Node(key, value, Color::RED);
    if (key < tp->key) {
      tp->left = x, x->parent = tp;
    } else {
      tp->right = x, x->parent = tp;
    }

    while (true) {
      auto* p1 = Parent(x);

      if (!is_red(x) || !is_red(p1)) // conformal to Tarjan invariant 2)
        break;

      // is_red(x) && is_red(Parent(x))
      // is_red(Parent(x)) ⇒ Grandparent(x) != nullptr

      auto* p2 = Grandparent(x);
      assert(p2);
      auto* p3 = Parent(Grandparent(x));

      if (is_red(p2->left) && is_red(p2->right)) {
        tarjan_promote(p2);
        x = p2;
      } else {
        bool p3_nil  = (p3 == nullptr);
        bool p2_left = !p3_nil && (p2 == p3->left); // p2 is a left child
        bool p1_left = (p1 == p2->left); // p1 is a left child
        bool x_left  = (x == p1->left); // x is a left child

        if (x_left && p1_left) {
          p2 = rotate_right(p2);
        } else if (!x_left && !p1_left) {
          p2 = rotate_left(p2);
        } else if (x_left) {
          assert(!p1_left);
          p2->right         = rotate_right(p2->right);
          p2->right->parent = p2;
          p2 = rotate_left(p2);
        } else {
          p2->left         = rotate_left(p2->left);
          p2->left->parent = p2;
          p2 = rotate_right(p2);
        }

        if (p3_nil) {
          t = p2;
        } else if (p2_left) {
          p3->left   = p2;
          p2->parent = p3;
        } else {
          p3->right  = p2;
          p2->parent = p3;
        }
        break;
      }
    }

    return t;
  }

  static Node* tarjan_delete (Node* t, const Key& key) {
    Node* x;
    std::tie(x, std::ignore) = find(t, key);
    if (nullptr == x) return t;

    // nullptr != x

    // Cases:
    //    1) x has null child.
    //    2) Both children of x are not null.

    if (nullptr == x->left || nullptr == x->right) {
      scoped_ptr<Node> retired;
      std::tie(x, retired) = retire(x);
    } else {
      assert(x->left != nullptr);
      auto* predecessor = rightmost(x->left);
      assert(predecessor != nullptr);

      std::swap(x->key, predecessor->key);
      std::swap(x->value, predecessor->value);

      x = predecessor;
      assert(nullptr == x->right);

      scoped_ptr<Node> retired;
      std::tie(x, retired) = retire(x);
    }

    
  }

  static void tarjan_promote (Node* t) { flip_colors(t); }

  static void tarjan_demote (Node* t) {

  }

  /**
   * @brief Given a node t, set the pointer fields in t to null.
   */
  static void detach (Node* t) {
    t->parent = t->left = t->right = nullptr;
  }

  /**
   * @brief Given a node x with exactly one child, replace x with its child and
   *    return the new x and the old.
   * @pre x has only one child.
   */
  static std::pair<Node*, Node*> retire (Node* x) {
    assert(x != nullptr);
    assert(x->left || x->right);
    assert(!(x->left && x->right));

    auto p = x->parent;
    auto c = (nullptr == x->left) ? x->right : x->left;

    c->parent = p;
    if (nullptr == p) void();
    else if (p->left == x) p->left = c;
    else p->right = c;

    detach(x);
    return {c, x};
  };

private:
  Node* root_;
};
