// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "ir/value.h"
#include "smt/expr.h"
#include "util/compiler.h"

using namespace smt;
using namespace util;
using namespace std;

static unsigned gbl_fresh_id = 0;

namespace IR {

void Value::reset_gbl_id() {
  gbl_fresh_id = 0;
}

string Value::fresh_id() {
  return to_string(++gbl_fresh_id);
}

expr Value::getTypeConstraints() const {
  return getType().getTypeConstraints();
}

void Value::fixupTypes(const Model &m) {
  type.fixup(m);
}

ostream& operator<<(ostream &os, const Value &val) {
  auto t = val.getType().toString();
  if (!t.empty())
    os << t << ' ';
  return os << val.getName();
}


IntConst::IntConst(Type &type, int64_t val)
  : Value(type, to_string(val)), val(val) {}

void IntConst::print(ostream &os) const {
  UNREACHABLE();
}

StateValue IntConst::toSMT(State &s) const {
  return { expr::mkInt(val, bits()), true };
}

expr IntConst::getTypeConstraints() const {
  unsigned min_bits = (val >= 0 ? 63 : 64) - num_sign_bits(val);
  return Value::getTypeConstraints() &&
         getType().enforceIntType() &&
         getType().sizeVar().uge(min_bits);
}


void UndefValue::print(ostream &os) const {
  UNREACHABLE();
}

StateValue UndefValue::toSMT(State &s) const {
  auto name = getFreshName();
  expr var = expr::mkVar(name.c_str(), bits());
  s.addUndefVar(var);
  return { move(var), true };
}

string UndefValue::getFreshName() {
  return "undef_" + fresh_id();
}


void PoisonValue::print(ostream &os) const {
  UNREACHABLE();
}

StateValue PoisonValue::toSMT(State &s) const {
  return { expr::mkUInt(0, bits()), false };
}


void Input::print(std::ostream &os) const {
  UNREACHABLE();
}

StateValue Input::toSMT(State &s) const {
  // 00: normal, 01: undef, else: poison
  expr type = getTyVar();

  auto bw = bits();
  string uname = UndefValue::getFreshName();
  expr undef = expr::mkVar(uname.c_str(), bw);
  s.addUndefVar(undef);

  return { expr::mkIf(type == expr::mkUInt(0, 2),
                      expr::mkVar(getName().c_str(), bw),
                      move(undef)),
           type.extract(1,1) == expr::mkUInt(0, 1) };
}

expr Input::getTyVar() const {
  string tyname = "ty_" + getName();
  return expr::mkVar(tyname.c_str(), 2);
}

}
