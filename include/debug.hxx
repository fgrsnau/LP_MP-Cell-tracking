#pragma once

namespace LP_MP {

template<typename CHECK> struct get_type;

template<class T>
std::string demangled_name(T &object)
{
  int status;
  char *demangled = abi::__cxa_demangle(typeid(object).name(), 0, 0, &status);
  if (status != 0)
    throw std::runtime_error("Demangling failed.");
  std::string result(demangled);
  free(demangled);
  return result;
}

template<typename ITERATOR>
struct print_iterator_helper
{
  print_iterator_helper(ITERATOR begin, ITERATOR end)
  : begin(begin)
  , end(end)
  { }

  ITERATOR begin;
  ITERATOR end;
};

template<typename ITERATOR>
print_iterator_helper<ITERATOR> print_iterator(ITERATOR begin, ITERATOR end)
{
  return print_iterator_helper<ITERATOR>(begin, end);
}

template<typename ITERATOR>
std::ostream& operator<<(std::ostream& o, const print_iterator_helper<ITERATOR> &pi)
{
  bool first = true;
  o << "[";
  for (ITERATOR it = pi.begin; it != pi.end; ++it) {
    if (!first)
      o << ", ";
    o << *it;
    first = false;
  }
  o << "]";
  return o;
}

template<typename CONTAINER>
auto print_container(const CONTAINER& c)
{
  return print_iterator(c.begin(), c.end());
}

} // namespace LP_MP
