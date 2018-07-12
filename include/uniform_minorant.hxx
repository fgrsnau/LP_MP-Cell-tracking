#pragma once
#ifndef LP_MP_UNIFORM_HXX
#define LP_MP_UNIFORM_HXX

#include "config.hxx"
#include "debug.hxx"
#include "vector.hxx"

namespace LP_MP {

// Last element of duals is "dummy" variable and no potentials gets distributed there!
//
// FIXME: Compute uniform minorant more efficiently.
vector<std::array<REAL,2>> uniform_minorant_generic(const vector<std::array<REAL,2>> &duals)
{
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

    for (INDEX i = 0; i < duals.size(); ++i) {
      for (bool on : {false, true}) {
        minorant[i][on] += epsilon * indicator[i][on];
        f_minus_g[i][on] -= epsilon * indicator[i][on];
      }
    }

    for (INDEX i = 0; i < duals.size(); ++i)
      indicator[i][i == argmin] = 0;
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
  : duals_(no_neighbors, 0)
  { }

  void init_primal()
  {
    WHERE_AM_I
    primal_ = std::numeric_limits<decltype(primal_)>::max();
  }

  REAL LowerBound() const
  {
    return std::min(duals_.min(), 0.0);
  }

  REAL EvaluatePrimal() const
  {
    if (primal_ < duals_.size())
      return duals_[primal_];
    else
      return 0.0;
  }

  template<typename ARCHIVE>
  void serialize_primal(ARCHIVE& a) { a(primal_); }

  template<typename ARCHIVE>
  void serialize_dual(ARCHIVE& a) { a(duals_); }

  auto export_variables() { return std::tie(/* duals_ */); }

  template<typename SOLVER>
  void construct_constraints(SOLVER& s /*, typename SOLVER::vector& v */) const { }

  template<typename SOLVER>
  void convert_primal(SOLVER& s /*, typename SOLVER::vector& v*/) { }

protected:
  vector<REAL> duals_;
  INDEX primal_;

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
    //assert(std::abs(omega - 1) < eps); // No longer valid.
    msg[0] -= l.min_detection_cost() * omega;
  }

  template<typename RIGHT_FACTOR, typename MSG_ARRAY>
  static void SendMessagesToLeft(const RIGHT_FACTOR& r, MSG_ARRAY msg_begin, MSG_ARRAY msg_end, const REAL omega)
  {
    //assert(std::abs(omega - 1) < eps);
#ifndef NDEBUG
    size_t count = 0;
    for (auto msg_it = msg_begin; msg_it != msg_end; ++msg_it)
      ++count;
    assert(count == r.duals_.size());
#endif

    // FIXME: Get rid of lifting.
    vector<std::array<REAL, 2>> lifted(r.duals_.size() + 1);
    for (size_t i = 0; i < r.duals_.size(); ++i)
      lifted[i] = {0, r.duals_[i]};
    lifted.back() = {0, 0};
    auto minorant = uniform_minorant_generic(lifted);
    assert(minorant.back()[0] == 0 && minorant.back()[1] == 0);

    size_t i = 0;
    for (auto msg_it = msg_begin; msg_it != msg_end; ++msg_it, ++i)
      (*msg_it)[0] -= (minorant[i][1] - minorant[i][0]) * omega;
  }

  template<typename RIGHT_FACTOR, typename G2>
  void send_message_to_left(RIGHT_FACTOR& r, G2& msg, const REAL omega)
  {
    assert(false);
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
    assert(index_ >= 0 && index_ < r.duals_.size());
    r.duals_[index_] += msg;
  }

  template<typename LEFT_FACTOR, typename RIGHT_FACTOR>
  bool ComputeRightFromLeftPrimal(const LEFT_FACTOR& l, RIGHT_FACTOR& r)
  {
    WHERE_AM_I
    assert(index_ >= 0 && index_ < r.duals_.size());
    if (l.detection_active() && r.primal_ >= r.duals_.size()) {
      r.primal_ = index_;
      return true;
    }
    return false;
  }

  template<typename LEFT_FACTOR, typename RIGHT_FACTOR>
  bool ComputeLeftFromRightPrimal(LEFT_FACTOR& l, const RIGHT_FACTOR& r)
  {
    WHERE_AM_I
    if (r.primal_ < r.duals_.size() && r.primal_ != index_) {
      const auto no_edge_taken = std::decay_t<decltype(l)>::no_edge_taken;
      if (l.incoming_edge_ != no_edge_taken || l.outgoing_edge_ != no_edge_taken) {
        l.incoming_edge_ = no_edge_taken;
        l.outgoing_edge_ = no_edge_taken;
        std::fill(l.incoming_edge_active_.begin(), l.incoming_edge_active_.end(), 0);
        std::fill(l.outgoing_edge_active_.begin(), l.outgoing_edge_active_.end(), 0);
        return true;
      }
    }
    return false;
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
