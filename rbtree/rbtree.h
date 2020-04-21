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
  scoped_ptr (T* p = nullptr) : std::unique_ptr<T>(p) { }
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
 *    A node is black is rank(p(x)) = rank(x) + 1 or p(x) is undefined,
 *    and red if rank(p(x)) = rank(x).
 */
class RBTree {
public:
  using Key = int;
  using Value = int;

  enum class Color : uint8_t {
    BLACK = 0,
    RED,
  };

  using Colorref = Color&;

  struct Node {
    Color color;
    Node* parent = nullptr;
    Node* left   = nullptr;
    Node* right  = nullptr;

    Key   key;
    Value value;

    Node (Key key, Value value, Color color)
        : key(key), value(value), color(color) { }

    void swap_payload (Node& other) {
      std::swap(key, other.key);
      std::swap(value, other.value);
    }

    friend void swap_payload (Node& lhs, Node& rhs) {
      lhs.swap_payload(rhs);
    }
  };

  using Nodeptr = Node*;
  using Nodepref = Nodeptr&;

  ~RBTree () { destroy(root_); }

  [[nodiscard]] bool is_empty () const { return Isnil(root_); }

  [[nodiscard]] Nodeptr min () const { return leftmost(root_); }

  [[nodiscard]] Nodeptr max () const { return rightmost(root_); }

  [[nodiscard]] std::string string_rep () const {
    return string_rep(root_);
  }

  static std::string string_rep (Nodeptr t) {

    auto key_rep = [] (Nodeptr t) -> std::string {
      return std::to_string(t->key) + (IsRed(t) ? "R" : "B");
    };

    if (Isnil(t)) {
      return ".";
    } else if (IsLeaf(t)) {
      return key_rep(t);
    } else {
      std::string left  = string_rep(Left(t)) + " ";
      std::string right = " " + string_rep(Right(t));
      return "(" + left + key_rep(t) + right + ")";
    }
  }

  /**
   * @brief Given a key, return the node corresponding to the greatest key less
   *  than or equal to the given key.
   *
   *  If no such node exists, return null.
   */
  [[nodiscard]] Nodeptr lower_bound (const Key& key) const {
    auto[u, p]= std::pair(Nodeptr(nullptr), root_);
    // Let P be the set of nodes that have been compared with the given key.
    // Let P' be { x ∈ P | x.key ≤ key }.
    // Invariant:
    //    Q(u): u is the node in P' with the maximum key.
    while (p) {
      if (int cmp = key_cmp(key, p->key); cmp < 0)
        p = Left(p);
      else if (cmp > 0)
        u = p, p = Right(p);
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
  Nodeptr predecessor (Nodeptr t) const {
    if (Isnil(t)) {
      return rightmost(root_);
    } else if (!Isnil(Left(t))) { // has left subtree
      return rightmost(Left(t));
    } else if (Isnil(Parent(t))) { // no left subtree ∧ be root
      // no left subtree ∧ be root ⇒ initial node
      return nullptr;
    } else if (Right(Parent(t)) == t) { // no left subtree ∧ be right child
      return Parent(t);
    } else { // no left subtree ∧ be left child
      // !Isnil(Parent(t))
      auto[u, pu] = ascend_rightward(Parent(t));
      // Isnil(pu) ∨ (!Isnil(pu) ∧ u == Right(pu))
      return pu;
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
  Nodeptr successor (Nodeptr t) const {
    if (Isnil(t)) {
      return leftmost(root_);
    } else if (!Isnil(Right(t))) { // has right subtree
      return leftmost(Right(t));
    } else if (Isnil(Parent(t))) { // no right subtree ∧ be root
      // no right subtree ∧ be root ⇒ final node
      return nullptr;
    } else if (Left(Parent(t)) == t) { // no right subtree ∧ be left child
      return Parent(t);
    } else { // no right subtree ∧ be right child

      // !Isnil(Parent(t))
      auto[u, pu] = ascend_leftward(Parent(t));
      // Isnil(pu) ∨ (!Isnil(pu) ∧ u == Left(pu))
      return pu;
    }
  }

  /**
   * @brief Given a key and a value, insert (key, value) into the search tree.
   *
   *  If key already exists in the search tree, replace the value.
   */
  void insert (Key key, Value value) {
    root_ = tarjan_insert(root_, key, value);
    Parent(root_) = nullptr;
    Color_(root_) = Color::BLACK;
  }

  /**
   * @brief Given a key, delete the node with the given key if any.
   */
  void erase (Key key) {
    assert(!Isnil(root_));
    Nodeptr excised;
    std::tie(root_, excised) = tarjan_delete(root_, key);
    if (Isnil(excised)) {
      throw std::runtime_error("The given key is not found.");
    } else {
      delete excised;
      if (!Isnil(root_)) {
        Parent(root_) = nullptr;
        Color_(root_) = Color::BLACK;
      }
    }
  }

protected:

  static bool Isnil (Nodeptr x) {
    return x == nullptr;
  }

  static bool IsLeft (Nodeptr x) {
    return Left(Parent(x)) == x;
  }

  static bool IsRight (Nodeptr x) {
    return Right(Parent(x)) == x;
  }

  static bool IsLeaf (Nodeptr x) {
    return Isnil(Left(x)) && Isnil(Right(x));
  }

  static Colorref Color_ (Nodeptr x) {
    return (*x).color;
  }

  static Nodepref Parent (Nodeptr x) {
    return (*x).parent;
  }

  static Nodepref Left (Nodeptr x) {
    return (*x).left;
  }

  static Nodepref Right (Nodeptr x) {
    return (*x).right;
  }

  static Nodepref Grandparent (Nodeptr x) {
    return Parent(Parent(x));
  }

  static Nodepref Sibling (Nodeptr x) {
    if (IsLeft(x))
      return Right(Parent(x));
    else
      return Left(Parent(x));
  }

  /**
   * @brief Given a node t, return whether the link pointing to its parent
   *  is red.
   * @note  IsRed(t) ⇒ (t != nullptr)
   */
  static bool IsRed (Nodeptr t) {
    if (Isnil(t)) return false;
    else return Color_(t) == Color::RED;
  }

  /**
   * @brief Given a node t and a key, return a pair (p, tp) such that p is the
   *    node with the given key under the subtree rooted at t, and tp (for
   *    "trailing pointer") is the parent of t.
   *
   *    If p is the root, return (p, null).
   *    If no such p is found, return (null, tp0) where tp0 is the last node
   *    checked before return.
   */
  static std::pair<Nodeptr, Nodeptr> find (Nodeptr t, const Key& key) {
    auto[p, tp]= std::pair(t, Nodeptr(nullptr));
    while (p) {
      if (int cmp = key_cmp(key, p->key); cmp < 0)
        tp = p, p = Left(p);
      else if (cmp > 0)
        tp = p, p = Right(p);
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
  static Nodeptr leftmost (Nodeptr t) {
    if (Isnil(t)) return nullptr;

    // t != nullptr
    auto[tp, p] = std::pair(t, Left(t));
    while (!Isnil(p)) {
      tp = p, p = Left(p);
    }
    return tp;
  }

  /**
   * @brief Given a node t, return the rightmost node in the subtree rooted
   *  at t.
   *
   *  In the case of null node, return null.
   */
  static Nodeptr rightmost (Nodeptr t) {
    if (Isnil(t)) return nullptr;

    // t != nullptr
    auto[tp, p] = std::pair(t, Right(t));
    while (!Isnil(p)) {
      tp = p, p = Right(p);
    }
    return tp;
  }

  static Nodeptr topmost (Nodeptr t) {
    auto[tp, p] = std::pair(Nodeptr(nullptr), t);
    while (!Isnil(p)) {
      tp = p, p = Parent(p);
    }
    return tp;
  }

  /**
   * @brief Given a node t, return a pair (u, pu) such that u is obtained by
   *  repeatedly following the edge to parent, starting from t, as long as the
   *  source is a left child.
   *
   *  The value of node pu is
   *    1) the parent of u, if u is the right child of its parent;
   *    2) null, otherwise.
   *
   * @pre t != nullptr
   * @post Isnil(pu) ∨ (!Isnil(pu) ∧ u == Right(pu))
   */
  static std::pair<Nodeptr, Nodeptr> ascend_rightward (Nodeptr t) {
    assert(!Isnil(t));

    auto[u, pu] = std::pair(t, Parent(t));
    while (!Isnil(pu) && u == Left(pu)) {
      u = pu, pu = Parent(pu);
    }
    // Isnil(pu) ∨ (!Isnil(pu) ∧ u == Right(pu))
    return {u, pu};
  }

  /**
   * @brief Given a node t, return a pair (u, pu) such that u is obtained by
   *  repeatedly following the edge to parent, starting from t, as long as the
   *  source is a right child.
   *
   *  The value of node pu is
   *    1) the parent of u, if u is the left child of its parent;
   *    2) null, otherwise.
   *
   * @pre   t != nullptr
   * @post  Isnil(pu) ∨ (!Isnil(pu) ∧ u == Left(pu))
   */
  static std::pair<Nodeptr, Nodeptr> ascend_leftward (Nodeptr t) {
    assert(!Isnil(t));

    auto[u, pu] = std::pair(t, Parent(t));
    while (!Isnil(pu) && u == Right(pu)) {
      u = pu, pu = Parent(pu);
    }
    // Isnil(pu) ∨ (!Isnil(pu) ∧ u == Left(pu))
    return {u, pu};
  }

  /**
   * @brief Given a node t, rotate right link to left and return the new root.
   *
   *  The parent links below the new root are well set. The parent link of the
   *  new root is not.
   *
   * @pre t && Right(t)
   * @invariant rotate_left() preserves invariant 1) and 4).
   */
  static Nodeptr rotate_left (Nodeptr t) {
    assert(t && Right(t));

    auto x = Right(t);
    // x != nullptr
    Right(t) = Left(x), Left(x) = t;
    std::swap(Color_(x), Color_(t));
    if (Right(t)) Parent(Right(t)) = t;
    Parent(t) = x;

    return x;
  }

  /**
   * @brief Given a node t, rotate left link to right and return the new root.
   *
   *  The parent links below the new root are well set. The parent link of the
   *  new root is not.
   *
   * @pre t && Left(t)
   * @invariant rotate_right() preserves invariant 1) and 4).
   */
  static Nodeptr rotate_right (Nodeptr t) {
    assert(t && Left(t));

    auto x = Left(t);
    // x != nullptr
    Left(t) = Right(x), Right(x) = t;
    std::swap(Color_(x), Color_(t));
    if (Left(t)) Parent(Left(t)) = t;
    Parent(t) = x;

    return x;
  }

  /**
   * @brief Given a node t, rotate right link of t to left, and return the new
   *   root with the parent link fixed up.
   */
  static Nodeptr rotate_left_with_fixup (Nodeptr t) {
    Nodeptr p      = Parent(t);
    bool    p_nil  = Isnil(p);
    bool    t_left = !p_nil && (Left(p) == t);

    t = rotate_left(t);
    Parent(t) = p;

    if (!p_nil && t_left) Left(p) = t;
    else if (!p_nil) Right(p) = t;

    return t;
  }

  /**
   * @brief Given a node t, rotate left link of t to right, and return the new
   *   root with the parent link fixed up.
   */
  static Nodeptr rotate_right_with_fixup (Nodeptr t) {
    Nodeptr p      = Parent(t);
    bool    p_nil  = Isnil(p);
    bool    t_left = !p_nil && (Left(p) == t);

    t = rotate_right(t);
    Parent(t) = p;

    if (!p_nil && t_left) Left(p) = t;
    else if (!p_nil) Right(p) = t;

    return t;
  }

  /**
   * @brief Given a node t, flip the colors of itself and its two children.
   */
  static void flip_colors (Nodeptr t) {
    Color_(t)        = flip(Color_(t));
    Color_(Left(t))  = flip(Color_(Left(t)));
    Color_(Right(t)) = flip(Color_(Right(t)));
  }

  /**
   * @post The new root is hung under the old parent of t.
   */
  static Nodeptr tarjan_insert (Nodeptr t, Key key, Value value) {

    auto[x, px] = find(t, key);

    // Cases:
    //  1) found
    //  2) empty tree
    //  3) nonempty tree and not found

    if (!Isnil(x)) { // Case 1)
      x->value = value;
      return t;
    } else if (Isnil(px)) { // Case 2)
      assert(Isnil(t));
      return new Node(key, value, Color::RED);
    }

    // Case 3)
    x = new Node(key, value, Color::RED);
    attach(x, px);

    while (true) {
      px = Parent(x);

      if (!IsRed(x) || !IsRed(px)) // conformal to Tarjan invariant 2)
        break;

      // IsRed(x) && IsRed(px)
      // IsRed(px) ⇒ !Isnil(Grandparent(x)) as there must be a black node
      //    in the path to the root.
      Nodeptr ppx = Parent(px);
      assert(ppx);

      if (IsRed(Left(ppx)) && IsRed(Right(ppx))) {
        tarjan_promote(ppx);
        x = ppx;
      } else {

        if (IsLeft(x)) {
          if (IsLeft(px)) { // zag-zag
            ppx = rotate_right_with_fixup(ppx);
          } else { // zig-zag
            Right(ppx)         = rotate_right(Right(ppx));
            Parent(Right(ppx)) = ppx;
            ppx = rotate_left_with_fixup(ppx);
          }
        } else {
          if (IsLeft(px)) { // zag-zig
            Left(ppx)         = rotate_left(Left(ppx));
            Parent(Left(ppx)) = ppx;
            ppx = rotate_right_with_fixup(ppx);
          } else { // zig-zig
            ppx = rotate_left_with_fixup(ppx);
          }
        }

        if (Isnil(Parent(ppx))) t = ppx;
        break;
      }
    }

    return t;
  }

  /**
   * @brief Given a node t, and a key, delete the node with the given key from
   *  the tree rooted at t, and return (t, excised) where t is the new root
   *  after deletion, and excised is the deleted node.
   */
  static std::pair<Nodeptr, Nodeptr> tarjan_delete (Nodeptr t, const Key& key) {
    Nodeptr x, px;
    std::tie(x, px) = find(t, key);
    // Invariant:
    //    !Isnil(x) ⇒ (px == Parent(x))
    assert(Isnil(x) || (px == Parent(x)));

    if (Isnil(x)) return {t, nullptr};
    // x0 := x

    // Cases:
    //    1) Node x has null child.
    //    2) Both children of x are not null.
    scoped_ptr<Node> excised;
    if (Isnil(Left(x)) || Isnil(Right(x))) {
      std::tie(x, px, excised) = excise(x);
    } else { // !Isnil(Left(x)) && !Isnil(Right(x))
      auto* pre = rightmost(Left(x));
      assert(!Isnil(pre) && Isnil(Right(pre)));
      swap_payload(*x, *pre);
      std::tie(x, px, excised) = excise(pre);
    }
    // excised == x0
    assert(!Isnil(excised.get()));

    if (IsRed(excised.get()) || IsRed(x)) { // conformal to property 1)
      if (!Isnil(x)) Color_(x) = Color::BLACK;
      return {Isnil(px) ? x : t,
              excised.release()};
    }
    // !IsRed(x0) && !IsRed(x)
    // rank(x) + 2 == rank(px)
    // Property 1) is violated.

    // Invariant:
    //    !Isnil(x0)
    auto YSibling = [] (Nodeptr x, Nodeptr px) -> Nodeptr {
      return !Isnil(x) ? Sibling(x) :
             !Isnil(Left(px)) ? Left(px) : Right(px);
    };

    while (!Isnil(px)) {
      // Property 1) is violated.
      Nodeptr y = YSibling(x, px);
      // !Isnil(px) && !Isnil(x0) && !IsRed(x0) ⇒ !Isnil(y)
      //    Case 1) x0 is equal to excised which is black.
      //    Case 2) x0 is as set in the loop body. Note that 
      //      ¬no_violation ⇔ !IsRed(x0).
      assert(!Isnil(y));

      if (IsRed(y)) { // Case 2
        if (IsLeft(y)) rotate_right_with_fixup(px);
        else rotate_left_with_fixup(px);
        y = YSibling(x, px);
      }
      assert(!IsRed(y));
      // Case 1
      if (!IsRed(Left(y)) && !IsRed(Right(y))) { // Case 1a
        bool no_violation = IsRed(px);
        // x0 := px
        { // Demote px.
          Color_(px) = Color::BLACK;
          Color_(y)  = Color::RED;
        }
        x = px, px = Parent(x);
        if (no_violation) break;
      } else if (IsRight(y)) { // IsLeft(x)
        if (IsRed(Right(y))) {
          // Case 1b
          px = rotate_left_with_fixup(px);
        } else {
          // Case 1c
          Right(px) = rotate_right(Right(px));
          px = rotate_left_with_fixup(px);
        }
        assert(IsRed(Right(px)));
        Color_(Right(px)) = Color::BLACK;
        break;
      } else {
        if (IsRed(Left(y))) {
          // Case 1b
          px = rotate_right_with_fixup(px);
        } else {
          // Case 1c
          Left(px) = rotate_left(Left(px));
          px = rotate_right_with_fixup(px);
        }
        assert(IsRed(Left(px)));
        Color_(Left(px)) = Color::BLACK;
        break;
      }
    }

    return {Isnil(px) ? x : topmost(px),
            excised.release()};
  }

  static void tarjan_promote (Nodeptr t) {
    assert(t && !IsRed(t) && IsRed(Left(t)) && IsRed(Right(t)));
    flip_colors(t);
  }

  /**
   * @brief Given a node t, set the pointer fields in t to null.
   */
  static void detach (Nodeptr t) {
    assert(t);
    Parent(t) = Left(t) = Right(t) = nullptr;
  }

  /**
   * @brief Given node x, node p, attach x under p.
   */
  static void attach (Nodeptr x, Nodeptr p) {
    if (int cmp = key_cmp(x->key, p->key); cmp < 0) {
      Left(p) = x, Parent(x) = p;
    } else {
      Right(p) = x, Parent(x) = p;
    }
  }

  /**
   * @brief Given a node x with at most one child, replace x with its child and
   *    return (new_x, px, old_x) which are the new x, the parent of x, and
   *    the old x.
   * @pre x has at most one child.
   */
  static std::tuple<Nodeptr, Nodeptr, Nodeptr> excise (Nodeptr x) {
    assert(!Isnil(x));
    assert(Isnil(Left(x)) || Isnil(Right(x)));

    auto px    = Parent(x);
    auto new_x = Isnil(Left(x)) ? Right(x) : Left(x);

    if (!Isnil(new_x)) Parent(new_x) = px;
    if (!Isnil(px) && Left(px) == x)
      Left(px) = new_x;
    else if (!Isnil(px)) // Right(px) == x
      Right(px) = new_x;

    detach(x);
    return {new_x, px, x};
  };

  /**
   * @brief Given a node t, destroy all the nodes in the subtree rooted at t.
   */
  static void destroy (Nodeptr t) {
    if (!Isnil(t)) {
      destroy(Left(t));
      destroy(Right(t));
      delete t;
    }
  }

  static int key_cmp (const Key& lhs, const Key& rhs) {
    if (lhs < rhs) return -1;
    else if (rhs < lhs) return 1;
    else return 0;
  }

  static Color flip (Color c) {
    switch (c) {
    case Color::BLACK:
      return Color::RED;
    case Color::RED:
      return Color::BLACK;
    }
  };

private:
  Nodeptr root_;
};
