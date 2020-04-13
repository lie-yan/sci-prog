//
// Created by Lie Yan on 2020/4/11.
//

#pragma once

#include <cstdint>

struct Node {
  using T = int;


  enum {
    BLACK,
    RED,
  };

  uint8_t color;
  Node *p;
  Node *left;
  Node *right;

  T payload;
};

