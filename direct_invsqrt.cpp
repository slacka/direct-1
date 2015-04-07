// The DIRECT-1 algorithm for minimizing a multidimensional function.
//    (searching for parameters of the inverse sqrt hack).
// Implementation 2010-02-13 by Jan "Rrrola" Kadlec. Public Domain.

#include <cmath>
#include <vector>
#include <queue>
#include <algorithm>

using std::max;
using std::min;
using std::sort;

// A point with fixed dimension.
template<int DIM>
struct Point
{ double x[DIM];
  double& operator[](int i) { return x[i]; }
  double operator[](int i) const { return x[i]; }

 // Construct a Point from DIM doubles (hack!).
  Point(){}
  Point(double x0) { x[0] = x0; }
  Point(double x0, double x1) { x[0] = x0; x[1] = x1; }
  Point(double x0, double x1, double x2) { x[0] = x0; x[1] = x1; x[2] = x2; }
  Point(double x0, double x1, double x2, double x3) { x[0] = x0; x[1] = x1; x[2] = x2; x[3] = x3; }
  Point(double x0, double x1, double x2, double x3, double x4) { x[0] = x0; x[1] = x1; x[2] = x2; x[3] = x3; x[4] = x4; }
};


// A boolean point with fixed dimension.
template<int DIM>
struct BoolPoint
{ bool x[DIM];
  bool& operator[](int i) { return x[i]; }
  bool operator[](int i) const { return x[i]; }
};


// A rectangle with an evaluated center - the basis of DIRECT.
// Allowed side lengths are (1/3)^level and (1/3)^(level+1).
template<int DIM>
struct Rectangle
{ double f;          // value at x[]
  Point<DIM> x;      // center coords
  BoolPoint<DIM> l;  // true = longer side, false = shorter side
};

template<int DIM>
bool operator<(Rectangle<DIM> const& a, Rectangle<DIM> const& b) { return a.f>b.f; }


// For sorting coordinates.
struct Index { double f; int index; };
bool operator<(Index const& a, Index const& b) { return a.f<b.f; }


//////////////////////////////////////////////////////////////////////////////


// Aggressive DIRECT-1.

// We have a pool of (hyper-)rectangles with evaluated f() in the center.
// Rectangles have a "level" according to their size, every side can be
// "long" or "short" (long = 3*short).

// Initial rectangle = whole area.
// 1. Choose rectangles to subdivide. For each:
//  2. Evaluate f(center +- side_length[d]/3) for all "long" dimensions.
//  3. Split central rectangle along all dimensions, starting from dims with
//     the best f().
// 4. Repeat.

// "-1" means that level = log(longest side). The original version
//   with level = ||center-vertex|| is too slow in aggressive mode.
// "Aggressive" means that we split the top rectangle in every level
//   without regard to its f(). This hurts only speed and simplifies
//   everything (the original version needs to compute the convex hull).
// - My improvement 1: just use a priority queue ;-)
// - My improvement 2: split only levels<threshold. Threshold changes when
//   solution didn't improve for a long time (Iterative Deepening FTW)

template<int DIM>
struct Direct
{ std::vector< Point<DIM> > scale;  // prec tables of length[d] * (1/3)^x
  std::vector< std::priority_queue< Rectangle<DIM> > > rectangle_set;
  double (*eval)(Point<DIM>&); int evals;
  double best_f; Point<DIM> best; int best_level;
  int maxlevel;

  void call_eval(Rectangle<DIM>& r, int level)
  { r.f = eval(r.x);
    if (best_f > r.f) best_f = r.f, best = r.x, best_level = level;
    evals++;
  }

 // Add a new rectangle into the pool.
  void add(Rectangle<DIM> const& r, int level)
  { if (rectangle_set.size() < level+1) rectangle_set.resize(level+1);
    rectangle_set[level].push(r);
  }

 // Initialize DIRECT with a rectangle covering the whole range.
  Direct(Point<DIM> const& l, Point<DIM> const& u, double (*eval)(Point<DIM>&))
  : best_f(HUGE_VAL), evals(0), eval(eval), rectangle_set(1), scale(1), maxlevel(4)
  { Rectangle<DIM> init;
    for (int i=0; i<DIM; i++) init.x[i] = 0.5 * (l[i]+u[i]);  // initial point
    for (int i=0; i<DIM; i++) init.l[i] = true;
    for (int i=0; i<DIM; i++) scale[0][i] = (u[i]-l[i]) * (1.0/3.0);
    call_eval(init, 0);
    add(init, 0);
  }

 // Pick the best rectangle in a given level and split it
  void split_top(int level)
  { if (level > maxlevel) return;
    Rectangle<DIM> r = rectangle_set[level].top();
    rectangle_set[level].pop();

   // Do shift tables need precomputation?
    if (scale.size() < level+1)
    { int size = scale.size();
      scale.resize(level+1);
      for ( ; size < scale.size(); ++size)
        for (int i=0; i<DIM; ++i) scale[size][i] = scale[size-1][i] * (1.0/3.0);
    }

    Rectangle<DIM> pos[DIM], neg[DIM];
    Index w[DIM];

   // For every long dimension of the rectangle:
   //  evaluate f(center+e_d) and f(center-e_d)
    int count=0;
    for (int i=0; i<DIM; i++) if (r.l[i])
    { pos[i].x = r.x; pos[i].x[i] += scale[level][i]; call_eval(pos[i], level);
      neg[i].x = r.x; neg[i].x[i] -= scale[level][i]; call_eval(neg[i], level);
      w[count].f = min(pos[i].f, neg[i].f);
      w[count].index = i;
      count++;
    }

   // Repeat:
   // Split the rectangle containing the center into thirds along
   //   the dimension with lowest f(center+-e_d).
   // Add the resulting rectangles into the pool
   //   (level = old level except for the last split, which gets level+1).
    std::sort(w, w+count);

    int i,j;
    BoolPoint<DIM> l = r.l;
    for (j=0; j<count-1; j++)
    { i = w[j].index;
      l[i] = false;
      pos[i].l = l; add(pos[i], level);
      neg[i].l = l; add(neg[i], level);
    }

    for (i=0; i<DIM; i++) l[i] = true;

    i = w[j].index;
    pos[i].l = l; add(pos[i], level+1);
    neg[i].l = l; add(neg[i], level+1);
    r.l = l;      add(r, level+1);
  }

 // Aggressive split: split the best rectangle in every level.
  void iter(void)
  { for (int i=min(rectangle_set.size()-1, (unsigned)maxlevel); i>=0; --i)
      if (!rectangle_set[i].empty())
        split_top(i);
  }
};

//////////////////////////////////////////////////////////////////////////////

#include "common.h"

union Float { float f; uint32 u; };

uint32 c1;
float c2, c3;

float inv_sqrt(float x)
{ Float y = {x};
  y.u = c1 - (y.u >> 1);
  return c2 * y.f * (c3 - x * y.f * y.f);
}


double relative_error(float f)
{
  return fabs(1.0 - (inv_sqrt(f) * sqrt(f)));
}

/////////////////////////////////////////

#define INITIAL_STEP 512
#define THOROUGH_PART 48

// Find the max relative error of a parameter set.
// Uses rough seeding at first, then scans around the highest seeds.
double max_relative_error(uint32 _c1, float _c2, float _c3)
{ c1 = _c1; c2 = _c2; c3 = _c3;

  Index errors[16777216/INITIAL_STEP];

  Float x;
  double maxerror = -HUGE_VAL;

 // initial seeding
  int i,j;
  for (i=0, x.f=1.0, x.u+=INITIAL_STEP/2; x.f<4.0f; x.u+=INITIAL_STEP, i++)
  { double error = relative_error(x.f);
    errors[i].f = -error;
    errors[i].index = x.u;
  }

 // find the seeds belonging to the highest (1/THOROUGH_PART)
  std::partial_sort(errors, errors+16777216/INITIAL_STEP/THOROUGH_PART, errors+16777216/INITIAL_STEP);

 // and thoroughly scan their surroundings
  for (i=0; i<16777216/INITIAL_STEP/THOROUGH_PART; i++)
  { for (x.u = errors[i].index-INITIAL_STEP/2; x.u < errors[i].index+INITIAL_STEP/2; x.u++)
    { double error = relative_error(x.f);
      maxerror = max(maxerror, error);
    }
  }
  return maxerror;
}



// Find the max relative error of a parameter set. Thorough scan (slow!).
double max_relative_error_exact(uint32 _c1, float _c2, float _c3)
{ c1 = _c1; c2 = _c2; c3 = _c3;

  Float x;
  double maxerror = -HUGE_VAL;

  for (x.f=1.0; x.f<4.0f; x.u++)
  { double error = relative_error(x.f);
    maxerror = max(maxerror, error);
  }
  return maxerror;
}



// Find the avg squared relative error of a parameter set.
// Simple rough seeding works well.
double avg_relative_error(uint32 _c1, float _c2, float _c3)
{ c1 = _c1; c2 = _c2; c3 = _c3;

  Float x;
  double sumerror = 0, sumerror2 = 0;
  int cnt = 0;

  for (x.f=1.0; x.f<4.0f; x.u+=79)
  { double error = relative_error(x.f);
    sumerror += error*error;
    cnt++;
    if ((cnt & 0xfff) == 0) sumerror2 += sumerror, sumerror = 0;
  }
  return (sumerror2 + sumerror) / cnt;
}


// Find the avg squared relative error of a parameter set. Thorough scan (slow!).
double avg_relative_error_exact(uint32 _c1, float _c2, float _c3)
{ c1 = _c1; c2 = _c2; c3 = _c3;

  Float x;
  double sumerror = 0, sumerror2 = 0;
  int cnt = 0;

  for (x.f=1.0; x.f<4.0f; x.u++)
  { double error = relative_error(x.f);
    sumerror += error*error;
    cnt++;
    if ((cnt & 0xfff) == 0) sumerror2 += sumerror, sumerror = 0;
  }
  return (sumerror2 + sumerror) / cnt;
}



#define DIMENSION 3

double eval(Point<DIMENSION>& p)
{
  return max_relative_error((uint32)p[0], p[1], p[2]);
//  return avg_relative_error((uint32)p[0], p[1], p[2]);
}


#include "random.c"

int main(void)
{

// min avg (relative_error^2)
//  Point<DIMENSION> low(0x5F1ACF80+randomAB(-10,10), 0.75589+random11()*0.000005, 2.27823+random11()*0.000005),
//                  high(0x5F1AD100+randomAB(-10,10), 0.75592+random11()*0.000005, 2.27833+random11()*0.000005);

// min max relative_error
//  Point<DIMENSION> low(0x5F1FF800+randomAB(-100,100), 0.7036+random11()*0.00002, 2.3901+random11()*0.00002),
//                  high(0x5F200800+randomAB(-100,100), 0.7043+random11()*0.00002, 2.3884+random11()*0.00002);
  Point<DIMENSION> low(0x5F601000+randomAB(-100,100), 0.24845+random11()*0.00002, 4.7825+random11()*0.00002),
                  high(0x5F602800+randomAB(-100,100), 0.24855+random11()*0.00002, 4.7840+random11()*0.00002);

  Direct<DIMENSION> D(low, high, eval);

  FILE* fw = fopen("direct_invsqrt.log.txt", "a"); if (!fw) return -1;


  int no_changes = 0, solution_age = 0, last_chars = 0, solution_chars = 0;
  double last_best = HUGE_VAL;

  for (int i=1; ; i++)
  {
    char s[128];
    snprintf(s, sizeof(s), "%d:%d:%d%n", i, D.evals, D.maxlevel, &last_chars);
    printf("\r%s", s);

    last_best = D.best_f;
    D.iter();

   // No improvement?
    if (last_best == D.best_f)
    {
     // If a few iters were unsuccessful, eval exactly and save current parameter set.
      if (++solution_age == 4)
//    { double error = avg_relative_error_exact((uint32)D.best[0], D.best[1], D.best[2]);
      { double error = max_relative_error_exact((uint32)D.best[0], D.best[1], D.best[2]);
        printf("\r"); for (int j=0; j<solution_chars-5; j++) printf(" ");
        printf("exact f=%.17g\n", error);
        fprintf(fw, "0x%8X %.9g %.9g  %.17g\n", (uint32)D.best[0], D.best[1], D.best[2], error);
      }

     // Random search: permute params with gaussian noise in several variance scales.
     // If better solution found, restart DIRECT centered on it (merged).
     // Beware: this can crawl out of the original bounds! I liked that, but
     //   you might want to all a test to prevent that.
      if (solution_age >= 16 && solution_age % 16 == 0)
      { uint k1 = D.best[0]; Float k2 = {D.best[1]}, k3 = {D.best[2]};
        uint l1; Float l2, l3;
        double min_e = D.best_f;
        bool changed_h = false;

        for (int h=256; h!=0; )
        { bool changed = false;
          printf("$");

          for (int i=0; i<8; i++)
          { l1 = k1 + randomNormal(0, h);
            l2.u = k2.u + randomNormal(0, h);
            l3.u = k3.u + randomNormal(0, h);
            double e = max_relative_error(l1, l2.f, l3.f);
            if (min_e > e)
            { D.best_f = min_e = e, changed = changed_h = true;
              D.best[0] = k1 = l1, D.best[1] = l2.f, k2.u = l2.u, D.best[2] = l3.f, k3.u = l3.u;
              printf("\r Rf=%.12g x=[0x%8X %.9g %.9g]\n", min_e, k1, k2.f, k3.f);
            }
          }

          if (!changed) h>>=1;
        }
        if (changed_h)
        { Rectangle<3> r = {min_e};
          r.x[0] = k1; r.x[1] = k2.f; r.x[2] = k3.f;
          r.l[0] = r.l[1] = r.l[2] = true;
          D.add(r, 1);
          solution_age = no_changes = 0;
        }
      }

     // If not improved in two random searches, try local deterministic grid search.
      if (solution_age == 33)
      { uint k1 = D.best[0]; Float k2 = {D.best[1]}, k3 = {D.best[2]};
        uint l1; Float l2, l3;
        double min_e = D.best_f;
        bool changed_h = false;

        for (int h=256; h!=0; )
        { bool changed = false;
          printf("#");

          for (int i=-h; i<=h; i+=h)
            for (int j=-h; j<=h; j+=h)
              for (int k=-h; k<=h; k+=h)
              { l1 = k1 + i;
                l2.u = k2.u + j;
                l3.u = k3.u + k;
                double e = max_relative_error(l1, l2.f, l3.f);
                if (min_e > e)
                { D.best_f = min_e = e, changed = changed_h = true;
                  D.best[0] = k1 = l1, D.best[1] = l2.f, k2.u = l2.u, D.best[2] = l3.f, k3.u = l3.u;
                  printf("\r Lf=%.12g x=[0x%8X %.9g %.9g]\n", min_e, k1, k2.f, k3.f);
                }
              }
          if (!changed) h>>=1;
        }
        if (changed_h)
        { Rectangle<3> r = {min_e};
          r.x[0] = k1; r.x[1] = k2.f; r.x[2] = k3.f;
          r.l[0] = r.l[1] = r.l[2] = true;
          D.add(r, 1);
          solution_age = no_changes = 0;
        }
      }

     // If no improvement for a long time, increase max rectangle level to split.
      if (++no_changes >= 30 && D.maxlevel < 10) D.maxlevel++, no_changes = 0;
    }

   // Found better solution! Joy!
    else
    { solution_age = no_changes = 0;
      solution_chars = last_chars;
      printf(" f=%.12g x=[0x%8X %.9g %.9g] l=%d\n", D.best_f, (uint32)D.best[0], D.best[1], D.best[2], D.best_level);
    }
  }

  return 0;
}
