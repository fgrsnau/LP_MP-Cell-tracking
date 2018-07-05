#pragma once
#ifndef LP_MP_UNIFORM_HXX
#define LP_MP_UNIFORM_HXX

#include "config.hxx"
#include "debug.hxx"
#include "vector.hxx"

namespace LP_MP {

template<typename T>
void print_array_container(const vector<std::array<T,2>>& c)
{
  bool first = true;
  std::cout << "[";
  for (auto& x : c) {
    if (!first)
      std::cout << ", ";
    std::cout << x[0] << ", " << x[1];
    first = false;
  }
  std::cout << "]";
}

vector<std::array<REAL,2>> uniform_minorant_generic(const vector<std::array<REAL,2>> &duals)
{
  if (debug()) {
    std::cout << "duals = "; print_array_container(duals); std::cout << std::endl;
  }

  const size_t dummy_index = duals.size() - 1;
  using minorant_type = vector<std::array<REAL,2>>;

  vector<std::array<int,2>> indicator(duals.size());
  minorant_type minorant(duals.size());
  minorant_type f_minus_g(duals.size()); // f - g

  for (INDEX i = 0; i < duals.size(); ++i) {
    for (bool on : { false, true }) {
      indicator[i][on] = 1;
      minorant[i][on] = 0;
      f_minus_g[i][on] = duals[i][on];
    }
  }
  indicator[dummy_index][0] = 0;
  indicator[dummy_index][1] = 0;

  auto continue_check = [](auto x) { return x[0] > 0 || x[1] > 0; };
  for (int iteration = 0; std::count_if(indicator.begin(), indicator.end(), continue_check) > 0; ++iteration) {
    INDEX argmin = std::numeric_limits<INDEX>::max();
    REAL min = std::numeric_limits<REAL>::infinity();
    for (INDEX i = 0; i < duals.size(); ++i) {
      INDEX h_x = 0;
      REAL current = 0;
      for (INDEX j = 0; j < duals.size(); ++j) {
        current += f_minus_g[j][i == j];
        if (indicator[j][i == j])
          ++h_x;
      }
      current /= h_x;
      if (h_x != 0 && current < min) {
        min = current;
        argmin = i;
      }
    }

    INDEX h_x = 0;
    for (INDEX i = 0; i < duals.size(); ++i)
      if (indicator[i][i == argmin])
        ++h_x;

    const REAL& epsilon = min;

    if (debug())
      std::cout << "[MINORANT] iteration = " << iteration << "  ->  argmin = " << argmin << " / h_x = " << h_x << " / epsilon = " << epsilon << std::endl;

    for (INDEX i = 0; i < duals.size(); ++i) {
      for (bool on : {false, true}) {
        minorant[i][on] += epsilon * indicator[i][on];
        f_minus_g[i][on] -= epsilon * indicator[i][on];
      }
    }

    for (INDEX i = 0; i < duals.size(); ++i)
      indicator[i][i == argmin] = 0;

    if (debug()) {
      std::cout << "indicator = "; print_array_container(indicator); std::cout << "\n";
      std::cout << "f_minus_g = "; print_array_container(f_minus_g); std::cout << "\n";
      std::cout << "minorant = "; print_array_container(minorant); std::cout << std::endl;
    }
  }

#ifndef NDEBUG
  for (INDEX on = 0; on < duals.size() - 1; ++on) {
    REAL o = 0, n = 0;
    for (INDEX i = 0; i < duals.size(); ++i) {
      o += duals[i][i == on];
      n += minorant[i][i == on];
    }
    assert(std::abs(o - n) < eps);
  }
#endif

  return minorant;
}

class uniform_minorant_factor {
public:
  uniform_minorant_factor(INDEX no_neighbors)
  : duals_(no_neighbors + 1)
  {
    for (auto& x : duals_)
      x = {0, 0};
  }

  void init_primal() { }

  REAL LowerBound() const {
    // FIXME
    REAL minimum = std::numeric_limits<REAL>::infinity();
    for (INDEX i = 0; i < duals_.size(); ++i)
      minimum = std::min(minimum, compute(i));
    return minimum;
  }

  REAL EvaluatePrimal() const {
    return 0;
  }

  template<typename ARCHIVE>
  void serialize_primal(ARCHIVE& a) { }

  template<typename ARCHIVE>
  void serialize_dual(ARCHIVE& a) { /* (duals_); */ }

  auto export_variables() { return std::tie(/* duals_ */); }

  template<typename SOLVER>
  void construct_constraints(SOLVER& s /*, typename SOLVER::vector& v */) const { }

  template<typename SOLVER>
  void convert_primal(SOLVER& s /*, typename SOLVER::vector& v*/) { }

  REAL compute(INDEX on) const
  {
    // FIXME: Remove this
    assert(on >= 0); assert(on < duals_.size());
    REAL sum = 0;
    for (INDEX i = 0; i < duals_.size(); ++i)
      sum += duals_[i][i == on ? 1 : 0];
    return sum;
  }

protected:
  vector<std::array<REAL,2>> duals_;

  friend class uniform_minorant_message;
};

class uniform_minorant_message {
public:
  uniform_minorant_message(INDEX index)
  : index_(index)
  { }

  template<typename LEFT_FACTOR, typename G2>
  void send_message_to_right(LEFT_FACTOR& l, G2& msg, const REAL omega)
  {
    /*
    std::cout << __PRETTY_FUNCTION__ << std::endl;
    std::cout << l.min_detection_cost() << std::endl;
    */

    assert(std::abs(omega - 1) < eps);
    msg[0] -= l.min_detection_cost() * omega;
  }

  template<typename RIGHT_FACTOR, typename MSG_ARRAY>
  static void SendMessagesToLeft(const RIGHT_FACTOR& r, MSG_ARRAY msg_begin, MSG_ARRAY msg_end, const REAL omega)
  {
    auto minorant = uniform_minorant_generic(r.duals_);
    assert(std::abs(omega - 1) < eps);

    //assert(std::distance(msg_begin, msg_end) == minorant.size() - 1);
#ifndef NDEBUG
    size_t count = 0;
    size_t idx_counter = 0;
    for (auto msg_it = msg_begin; msg_it != msg_end; ++msg_it) {
      ++count;
      idx_counter += (*msg_it).GetMessageOp().index_;
      }
      assert(idx_counter == (minorant.size()-1)*(minorant.size()-2)/2);
    assert(count == minorant.size() - 1);
#endif

    size_t i = 0;
    for (auto msg_it = msg_begin; msg_it != msg_end; ++msg_it, ++i) {
      (*msg_it)[0] -= (minorant[i][1] - minorant[i][0]) * omega;
    }
  }

  template<typename RIGHT_FACTOR, typename G2>
  void send_message_to_left(RIGHT_FACTOR& r, G2& msg, const REAL omega)
  {
    assert(false);

    // TODO: Check this.
#if 0
    std::cout << __PRETTY_FUNCTION__ << "\n" << omega << " / " << r.duals_.size() << std::endl;
    assert(index_ >= 0 && index_ < r.duals_.size());
    assert(std::abs(omega * r.duals_.size() - 1) < eps);
    msg[0] -= r.duals_[index_];
#endif
  }

  template<typename LEFT_FACTOR>
  void RepamLeft(LEFT_FACTOR& l, const REAL msg, const INDEX msg_dim)
  {
    assert(msg_dim == 0);
    l.detection += msg;
  }

  template<typename RIGHT_FACTOR>
  void RepamRight(RIGHT_FACTOR& r, const REAL msg, const INDEX msg_dim)
  {
    assert(msg_dim == 0);
    assert(index_ >= 0 && index_ < r.duals_.size() - 1);
    /*
    std::cout << "r.duals_[" << index_ << "][1] += " << msg << std::endl;
    */
    r.duals_[index_][1] += msg;
    assert(r.duals_[index_][0] == 0);
  }

  template<typename SOLVER, typename LEFT_FACTOR, typename RIGHT_FACTOR>
  void construct_constraints(SOLVER& s,
    LEFT_FACTOR& left, typename SOLVER::variable left_detection_var, typename SOLVER::vector left_incoming_vars, typename SOLVER::vector left_outgoing_vars,
    RIGHT_FACTOR& right /*, typename SOLVER::vector& v2*/ ) const { }

protected:
  INDEX index_;
};

} // namespace LP_MP

#endif
