/*
Copyright (c) 2008 - 2010, Armin Biere, Johannes Kepler University.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal in the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
IN THE SOFTWARE.
*/

#include "../aiger/aiger.h"
#include "../picosat/picosat.h"

unsigned picosat_ado_conflicts (void);
void picosat_disable_ado (void);
void picosat_enable_ado (void);
void picosat_set_ado_conflict_limit (unsigned limit);

#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <stdarg.h>
#include <limits.h>
#include <ctype.h>
#include <signal.h>
#include <unistd.h>

#define SAT PICOSAT_SATISFIABLE
#define UNSAT PICOSAT_UNSATISFIABLE

static aiger * model;
static int verbosity;
static double start;

static int witness;
static int ionly, bonly;
static int dcs, acs, rcs, mix, ncs;
static unsigned * frames, sframes, nframes;
static unsigned nrcs;

static void
die (const char * fmt, ...)
{
  va_list ap;
  fprintf (stderr, "*** mcaiger: ");
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void
catch (int sig)
{
  fprintf (stderr, "*** mcaiger: caught signal(%d)\n", sig);
  fflush (stderr);

  if (verbosity > 1)
    picosat_stats ();

  fflush (stderr);

  kill (getpid (), sig);
}

static void
catchall (void)
{
  struct sigaction action;
  memset (&action, 0, sizeof action);
  action.sa_handler = catch;
  action.sa_flags = SA_NODEFER | SA_RESETHAND;
  sigaction (SIGSEGV, &action, 0);
  sigaction (SIGTERM, &action, 0);
  sigaction (SIGINT, &action, 0);
  sigaction (SIGABRT, &action, 0);
}

static void
msg (int level, int include_time, const char * fmt, ...)
{
  double delta;
  va_list ap;

  if (verbosity < level)
    return;

  fprintf (stderr, "[mcaiger] ");
  if (include_time)
    {
      delta = picosat_time_stamp () - start;
      fprintf (stderr, "%4.1f ", delta < 0.0 ? 0.0 : delta);
    }
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
}

static int
frame (int k)
{
  int res;

  res = k * model->maxvar + 2;
  if (dcs || rcs || mix)
    res += model->num_latches * k * (k - 1) / 2;

  return res;
}

static int
lit (unsigned k, unsigned l)
{
  int res;
  assert (0 <= l && l <= 2 * model->maxvar + 1);
  res =  (l <= 1) ? 1 : frame (k) + (int)((l - 2)/2);
  if (l & 1)
    res = -res;
  return res;
}

static int
input (unsigned k, unsigned i)
{
  assert (0 <= i && i < model->num_inputs);
  return lit (k, model->inputs[i].lit);
}

static int
latch (unsigned k, unsigned i)
{
  assert (0 <= i && i < model->num_latches);
  return lit (k, model->latches[i].lit);
}

static int
next (unsigned k, unsigned i)
{
  assert (0 <= i && i < model->num_latches);
  return lit (k, model->latches[i].next);
}

static int
output (unsigned k, unsigned i)
{
  assert (0 <= i && i < model->num_outputs);
  return lit (k, model->outputs[i].lit);
}

static void
unary (int a)
{
  assert (a);
  picosat_add (a);
  picosat_add (0);
}

static void
binary (int a, int b)
{
  assert (a);
  picosat_add (a);
  assert (b);
  picosat_add (b);
  picosat_add (0);
}

static void
ternary (int a, int b, int c)
{
  assert (a);
  picosat_add (a);
  assert (b);
  picosat_add (b);
  assert (c);
  picosat_add (c);
  picosat_add (0);
}

static void
and (int lhs, int rhs0, int rhs1)
{
  binary (-lhs, rhs0);
  binary (-lhs, rhs1);
  ternary (lhs, -rhs0, -rhs1);
}

static void
eq (int lhs, int rhs)
{
  binary (-lhs, rhs);
  binary (lhs, -rhs);
}

static void
report (int verbosity, unsigned k, const char * phase)
{
  msg (verbosity, 1,
       "%4u %-10s %10d %11d %11u",
       k, phase, 
       picosat_variables (), picosat_added_original_clauses (),
       picosat_ado_conflicts ());
}

static void
connect (unsigned k)
{
  unsigned i;

  if (!k)
    return;

  for (i = 0; i < model->num_latches; i++)
    eq (next (k-1, i), latch (k, i));

  report (2, k, "connect");
}

static void
encode (unsigned k)
{
  aiger_and * a;
  unsigned i;

  if (!k)
    unary (lit (k, 1));		/* true */

  for (i = 0; i < model->num_ands; i++)
    {
      a = model->ands + i;
      and (lit (k, a->lhs), lit (k, a->rhs0), lit (k, a->rhs1));
    }

  if (k)
    {
      for (i = 0; i < model->num_latches; i++)
	picosat_add (latch (k, i));

      picosat_add (0);

      unary (-output (k - 1, 0));
    }

  report (2, k, "encode");
}

static void
ado (unsigned k)
{
  unsigned i;

  for (i = 0; i < model->num_latches; i++)
    picosat_add_ado_lit (latch (k, i));

  picosat_add_ado_lit (0);

  report (2, k, "ado");
}

static int
diff (int k, int l, int i)
{
  assert (0 <= i && i < model->num_latches);
  assert (l < k);
  return frame (k + 1) - i - l * model->num_latches - 1;
}

static void
diffs (unsigned k, unsigned l)
{
  unsigned i, tmp;

  assert (k != l);

  if (l > k)
    {
      tmp = k;
      k = l;
      l = tmp;
    }

  for (i = 0; i < model->num_latches; i++)
    {
      ternary (latch (l, i), latch (k, i), -diff (k, l, i));
      ternary (-latch (l, i), -latch (k, i), -diff (k, l, i));
    }

  for (i = 0; i < model->num_latches; i++)
    picosat_add (diff (k, l, i));

  picosat_add (0);

  msg (2, 1, "diffs %u %u", l, k);
}

static void
diffsk (unsigned k)
{
  unsigned l;

  if (!k)
    return;

  for (l = 0; l < k; l++)
    diffs (k, l);

  report (2, k, "diffsk");
}

static void
simple (unsigned k)
{
  if (dcs)
    diffsk (k);
  else if (acs)
    ado (k);
  else
    assert (rcs || ncs);
}

static void
stimulus (unsigned k)
{
  unsigned i, j;
  int tmp;

  for (i = 0; i <= k; i++)
    {
      for (j = 0; j < model->num_inputs; j++)
	{
	  tmp = picosat_deref (input (i, j));
	  fputc (tmp ? ((tmp < 0) ? '0' : '1') : 'x', stdout);
	}

      fputc ('\n', stdout);
    }
}

static void
bad (unsigned k)
{
  assert (model->num_outputs == 1);
  picosat_assume (output (k, 0));
  report (2, k, "bad");
}

static void
init (unsigned k)
{
  unsigned i;
  int l;

  if (bonly && k)
    return;

  for (i = 0; i < model->num_latches; i++)
    {
      l = -latch (0, i);
      if (bonly)
	unary (l);
      else
	picosat_assume (l);
    }

  report (2, k, "init");
}

static int
cmp_frames (const void * p, const void * q)
{
  unsigned k = *(unsigned *) p;
  unsigned l = *(unsigned *) q;
  int a, b, res;
  unsigned i;

  for (i = 0; i < model->num_latches; i++)
    {
      a = picosat_deref (latch (k, i));
      b = picosat_deref (latch (l, i));
      res = a - b;
      if (res)
	return res;
    }

  return 0;
}

static int
sat (unsigned k)
{
  unsigned i;
  int res;

  if (rcs || mix)
    {
      if (k == nframes)
	{
	  assert (k == nframes);

	  if (k >= sframes)
	    {
	      sframes = sframes ? 2 * sframes : 1;
	      frames = realloc (frames, sframes * sizeof frames[0]);
	    }

	  assert (nframes < sframes);
	  frames[nframes++] = k;
	}

      assert (nframes == k + 1);
    }

RESTART:
  res = picosat_sat (-1);

  if (res == UNSAT)
    return res;

  if (res == SAT && !rcs)
    return res;

  if (!res)
    {
      assert (mix);
      assert (!rcs);
      assert (acs);
      rcs = 1;
      acs = 0;
      picosat_disable_ado ();
      goto RESTART;
    }

  assert (rcs);
  assert (res == SAT);

  qsort (frames, k + 1, sizeof frames[0], cmp_frames);
  for (i = 0; i < k; i++)
    if (!cmp_frames (frames + i, frames + i + 1))
      {
	diffs (frames[i], frames[i+1]);
	nrcs++;
	bad (k);
	goto RESTART;
      }

  assert (i == k);	/* all different */

  return SAT;
}

static int
step (unsigned k)
{
  int res;
  if (mix && acs)
    picosat_set_ado_conflict_limit (picosat_ado_conflicts () + 1000);
  bad (k);
  report (1, k, "step");
  res = (sat (k) == UNSAT);

  return res;
}

static int
base (unsigned k)
{
  int res;
  if (acs) 
    picosat_disable_ado ();
  init (k);
  bad (k);
  report (1, k, "base");
  res = (sat (k) == SAT);
  if (acs) 
    picosat_enable_ado ();
  return res;
}

#define USAGE \
"mcaiger [<option> ...][<aiger>]\n" \
"\n" \
"where <option> is one of the following:\n" \
"\n" \
"  -h       print this command line summary and exit\n" \
"  -v       increase verbosity (default 0, max 3)\n" \
"  -b       base case only (only search for witnesses)\n" \
"  -i       inductive case only\n" \
"  -a       use all different contraints (default)\n" \
"  -r       incremental refinement of simple path constraints\n" \
"  -m       mix '-a' and '-r'\n" \
"  -d       use classical SAT encoding of simple path constraints\n" \
"  -n       no simple path nor all different constraints\n" \
"  -w       print witness\n" \
"  <maxk>   maximum bound\n"

int
main (int argc, char ** argv)
{
  const char * name = 0, * err;
  unsigned k, maxk = UINT_MAX;
  int i, cs, res;
  double delta;

  start = picosat_time_stamp ();

  for (i = 1; i < argc; i++)
    {
      if (!strcmp (argv[i], "-h"))
	{
	  fprintf (stderr, USAGE);
	  exit (0);
	}
      else if (!strcmp (argv[i], "-v"))
	verbosity++;
      else if (!strcmp (argv[i], "-b"))
	bonly = 1;
      else if (!strcmp (argv[i], "-i"))
	ionly = 1;
      else if (!strcmp (argv[i], "-a"))
	acs = 1;
      else if (!strcmp (argv[i], "-d"))
	dcs = 1;
      else if (!strcmp (argv[i], "-r"))
	rcs = 1;
      else if (!strcmp (argv[i], "-m"))
	mix = 1;
      else if (!strcmp (argv[i], "-n"))
	ncs = 1;
      else if (!strcmp (argv[i], "-w"))
	witness = 1;
      else if (isdigit (argv[i][0]))
	maxk = (unsigned) atoi (argv[i]);
      else if (argv[i][0] == '-')
	die ("invalid command line option '%s'", argv[i]);
      else if (name)
	die ("multiple input files '%s' and '%s'", name, argv[i]);
      else
	name = argv[i];
    }

  if (ionly && bonly)
    die ("'-i' and '-b' can not be combined");

  cs = dcs + acs + rcs + mix + ncs;
  if (cs > 1)
    die ("at most one of '-a', '-r', '-m', '-d', or '-n' can be used");

  if (bonly && (cs && !ncs))
    die ("can not combine '-b' with '-[armd]'");

  if (bonly)
    ncs = cs = 1;

  if (!cs || mix)
    acs = 1;

  model = aiger_init ();

  msg (1, 0, "McAIGer Version 2");
  msg (1, 0, "parsing %s", name ? name : "<stdin>");

  if (name)
    err = aiger_open_and_read_from_file (model, name);
  else
    err = aiger_read_from_file (model, stdin);

  if (err)
    die (err);

  if (!model->num_outputs)
    die ("no output found");

  if (model->num_outputs > 1)
    die ("more than one output found");

  aiger_reencode (model);

  msg (1, 0, "%u literals (MILOA %u %u %u %u %u)",
       model->maxvar + 1,
       model->maxvar,
       model->num_inputs,
       model->num_latches,
       model->num_outputs,
       model->num_ands);

  picosat_init ();

  catchall ();

  picosat_set_prefix ("[picosat] ");
  picosat_set_output (stderr);

  if (verbosity > 2)
    picosat_enable_verbosity ();

  res = 0;
  for (k = 0; k <= maxk; k++)
    {

      if (mix && acs && picosat_ado_conflicts () >= 10000)
	{
	  acs = 0;
	  rcs = 1;
	  picosat_disable_ado ();
	}

      connect (k);
      encode (k);
      simple (k);

      if (!bonly && step (k))
	{
	  report (1, k, "inductive");
	  fputs ("0\n", stdout);
	  res = 20;
	  break;
	}

      if (bonly && picosat_inconsistent ())
	{
	  report (1, k, "inconsistent");
	  fputs ("0\n", stdout);
	  res = 20;
	  break;
	}

      if (!ionly && base (k))
	{
	  report (1, k, "reachable");
	  fputs ("1\n", stdout);
	  if (witness)
	    stimulus (k);
	  res = 10;
	  break;
	}
    }

  if (!res) {
    assert (k > maxk);
    fputs ("2\n", stdout);
  }

  fflush (stdout);

  if (verbosity > 1)
    picosat_stats ();

  picosat_reset ();
  aiger_reset (model);

  free (frames);

  if (rcs || mix)
    msg (1, 0, "%u refinements of simple path constraints", nrcs);

  delta = picosat_time_stamp () - start;
  msg (1, 0, "%.1f seconds", delta < 0.0 ? 0.0 : delta);

  return res;
}
