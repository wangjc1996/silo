  /**
 * An implementation of TPC-C based off of:
 * https://github.com/oltpbenchmark/oltpbench/tree/master/src/com/oltpbenchmark/benchmarks/tpcc
 */

#include <sys/time.h>
#include <string>
#include <ctype.h>
#include <stdlib.h>
#include <malloc.h>

#include <stdlib.h>
#include <unistd.h>
#include <getopt.h>

#include <set>
#include <vector>

#include "../txn.h"
#include "../macros.h"
#include "../scopedperf.hh"
#include "../spinlock.h"

#include "bench.h"
#include "micro_bench.h"
#include "ndb_wrapper.h"
#include "ndb_wrapper_impl.h"

using namespace std;
using namespace util;

#define PINCPU
#define MAXCPU 64

#define TEST_TABLE_LIST(x) \
  x(test) 


static const size_t TXTTPES = 1;

static const size_t records_per_table = 10000;
static bool profile = false;
static size_t txn_length = 10;
static float conflict_rate = 1.0/records_per_table;
static float user_abort_rate = 0;
static uint64_t access_range = 10;

static float read_rate = 0;
static int read_first = 0;

static unsigned g_txn_workload_mix[] = {100};

#define PROFILE


struct micro_profile {

  uint64_t gettime = 0;
  uint64_t puttime = 0;
  uint64_t piecestarttime = 0;
  uint64_t piececommittime = 0;
  uint64_t txnstarttime = 0;
  uint64_t txncommittime = 0;
  uint64_t succ = 0;

  micro_profile()
  {
    gettime = 0;
    puttime = 0;
    piecestarttime = 0;
    piececommittime = 0;
    txnstarttime = 0;
    txncommittime = 0;
    succ = 0;
  }

  micro_profile& operator+=(const micro_profile& p)
  {                           
    gettime += p.gettime;
    puttime += p.puttime;
    piecestarttime += p.piecestarttime;
    piececommittime += p.piececommittime;
    txnstarttime += p.txnstarttime;
    txncommittime += p.txncommittime;
    succ += p.succ;

    return *this; 
  }

  void print_avg()
  {
    fprintf(stderr, "SUCC[%ld] BEG[TXN]: %ld END[TXN]: %ld BEG[P]: %ld END[P]: %ld GET %ld PUT %ld\n", 
      succ, txnstarttime/succ, txncommittime/succ, 
      piecestarttime/succ, piececommittime/succ, 
      gettime/succ, puttime/succ);
  }

} CACHE_ALIGNED;

static micro_profile pdata[MAXCPU];

static void print_profile() 
{
  if(!profile)
    return;

  micro_profile avg_prof;

  for(int i = 0; i < MAXCPU; i++) {
    avg_prof += pdata[i];
  }

  avg_prof.print_avg();
}



enum  MICRO_TYPES
{
  MICROBENCH = 1,
};


static inline ALWAYS_INLINE int
CheckBetweenInclusive(int v, int lower, int upper)
{
  INVARIANT(v >= lower);
  INVARIANT(v <= upper);
  return v;
}

static inline ALWAYS_INLINE int
RandomNumber(fast_random &r, int min, int max)
{
  return CheckBetweenInclusive((int) (r.next_uniform() * (max - min + 1) + min), min, max);
}

static inline ALWAYS_INLINE int
NonUniformRandom(fast_random &r, int A, int C, int min, int max)
{
  return (((RandomNumber(r, 0, A) | RandomNumber(r, min, max)) + C) % (max - min + 1)) + min;
}


static inline void 
bind_thread(uint worker_id)
{

#ifdef PINCPU
  const size_t cpu = worker_id % coreid::num_cpus_online();
  cpu_set_t cpuset;
  CPU_ZERO(&cpuset);
  CPU_SET(cpu, &cpuset);
  int s = pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);
  if (s != 0)
      fprintf(stderr, "pthread_setaffinity_np");
#endif

}


class micro_worker : public bench_worker {
public:
  micro_worker(unsigned int worker_id,
              unsigned long seed, abstract_db *db,
              const map<string, abstract_ordered_index *> &open_tables,
              spin_barrier *barrier_a, spin_barrier *barrier_b)
    : bench_worker(worker_id, true, seed, db,
                   open_tables, barrier_a, barrier_b),
      tbl(open_tables.at("TESTTABLE")),
      computation_n(0),
      pidx(0)
  {}

  txn_result
  txn_micro()
  {

    string obj_buf;
    bool res = false;

    size_t read_records = read_rate * txn_length;
    size_t write_records = txn_length - read_records;


    uint64_t beg_time = 0;
    if(profile)
      beg_time = rdtsc();

    scoped_str_arena s_arena(arena);
    void * const txn = db->new_txn(txn_flags, arena, txn_buf(), abstract_db::HINT_MICRO);

    if(profile)
      pdata[pidx].txnstarttime += rdtsc() - beg_time;


    try {

        for(size_t i = 0; i < txn_length; i++) {

            int min = 0;
            int max = 0;

            if(conflict_rate == 0) {

              min = i * records_per_table + (records_per_table / MAXCPU) * (worker_id % MAXCPU);

              max = i * records_per_table + (records_per_table / MAXCPU) * ((worker_id  + 1 )% MAXCPU) - 1;

            } else {

              min = i * records_per_table;
              max = i * records_per_table + access_range - 1;
    
            }

            uint32_t n =  RandomNumber(r, min, max);


            // printf("Thread{%d} n %lu min %lu max %lu\n", worker_id, n, i*records_per_table, i * records_per_table + access_range - 1);
            // n += i * records_per_table;

            const test::key k(n);
            string test_v;


            uint64_t get_beg = 0;
            if(profile)
              get_beg = rdtsc();


            ALWAYS_ASSERT(tbl->get(txn, Encode(obj_key0, k), test_v));
            
            if(profile)
              pdata[pidx].gettime += rdtsc() - get_beg ;


            test::value temp; 
            const test::value *v = Decode(test_v, temp);

            if(read_first && read_records > 0)
              read_records--;
            
            if((read_first && read_records == 0) ||
              ((!read_first) && write_records > 0)) {

              test::value v_new(*v);
              v_new.t_v_count++;   
              ALWAYS_ASSERT(v_new.t_v_count > 0);


              uint64_t put_beg = 0;
              if(profile)
                put_beg = rdtsc();


              tbl->put(txn, Encode(str(), k), Encode(str(), v_new));

              if(profile)
                pdata[pidx].puttime += rdtsc() - put_beg ;


              if(!read_first)
                write_records--;
            }

        }


        uint64_t end_txn_beg = 0;
        if(profile)
          end_txn_beg = rdtsc();


        //fprintf(stderr, "%ld, %ld, %ld\n", oldv, newv, coreid::core_id());
        res = db->commit_txn(txn);
        //ALWAYS_ASSERT(res);

        if(profile) {
          pdata[pidx].txncommittime += rdtsc() - end_txn_beg ;
          pdata[pidx].succ++;
        }


      } catch (abstract_db::abstract_abort_exception &ex) {
  
        db->abort_txn(txn);
      }

    return txn_result(res, 0);
  }

  static txn_result
  TxnMicro(bench_worker *w)
  {
    return static_cast<micro_worker *>(w)->txn_micro();
  }

  virtual workload_desc_vec
  get_workload() const
  {
  
    workload_desc_vec w;
    unsigned m = 0;
    for (size_t i = 0; i < ARRAY_NELEMS(g_txn_workload_mix); i++)
      m += g_txn_workload_mix[i];
    ALWAYS_ASSERT(m == 100);
    if (g_txn_workload_mix[0])
      w.push_back(workload_desc("Micro bench",  double(g_txn_workload_mix[0])/100.0, TxnMicro));
    
    return w;
  }

protected:

  virtual void
  on_run_setup() OVERRIDE
  {
    
    bind_thread(worker_id);
    pidx = worker_id - coreid::num_cpus_online();
  }

  inline ALWAYS_INLINE string &
  str() {
    return *arena.next();
  }

private:
  abstract_ordered_index *tbl;

  string obj_key0;
  string obj_key1;
  string obj_v;

  uint64_t computation_n;
  uint32_t pidx;
};

class microbench_loader : public bench_loader{

public:
  microbench_loader(unsigned long seed,
                        abstract_db *db,
                        const map<string, abstract_ordered_index *> &open_tables,
                        int table)
    : bench_loader(seed, db, open_tables), table_id(table)
  {}

protected:
  virtual void
  load()
  {

    abstract_ordered_index *tbl = open_tables.at("TESTTABLE");
    string obj_buf;
    size_t batch_size = 1000;
    ALWAYS_ASSERT(records_per_table > batch_size && records_per_table % batch_size == 0);

    // size_t min = table_id * records_per_table / batch_size;
    // size_t max = (table_id + 1) * records_per_table / batch_size;

    size_t min = 0;
    size_t max = (txn_length + 1) * records_per_table / batch_size;

    scoped_str_arena s_arena(arena);
    
    for(size_t i = min; i < max; i++)
    {

      void * const txn = db->new_txn(txn_flags, arena, txn_buf(), abstract_db::HINT_MICRO_LOADER);
      try {

        for (size_t n = i * batch_size; n < (i + 1) * batch_size; n++) {
            // printf("load %lu in table %d\n", n, table_id);
            const test::key k(n);
            const test::value v(0, "TEST");
            tbl->insert(txn, Encode(k), Encode(obj_buf, v));

        }

        bool res = db->commit_txn(txn);
        ALWAYS_ASSERT(res);

      } catch (abstract_db::abstract_abort_exception &ex) {
        ALWAYS_ASSERT(false);
        db->abort_txn(txn);
      }
    }
    
    printf("Load Done [%d]\n", table_id);
  }

private:
  int table_id;
};





class micro_bench_runner : public bench_runner {
public:
  micro_bench_runner(abstract_db *db)
    : bench_runner(db)
  {
    open_tables["TESTTABLE"] = db->open_index("TESTTABLE", (txn_length * records_per_table));
  }

protected:
  virtual vector<bench_loader *>
  make_loaders()
  {
    vector<bench_loader *> ret;

    // for(size_t i = 0; i < txn_length; i++)
      ret.push_back(new microbench_loader(0, db, open_tables, 0));
   
    return ret;
  }

  virtual vector<bench_worker *>
  make_workers()
  {
    const unsigned alignment = coreid::num_cpus_online();
    const int blockstart =
      coreid::allocate_contiguous_aligned_block(nthreads, alignment);
    ALWAYS_ASSERT(blockstart >= 0);
    ALWAYS_ASSERT((blockstart % alignment) == 0);
    fast_random r(8544290);
    vector<bench_worker *> ret;
    for (size_t i = 0; i < nthreads; i++)
      ret.push_back(
        new micro_worker(
          blockstart + i, r.next(), db, open_tables,
          &barrier_a, &barrier_b));
    return ret;
  }



};

void
microbench_do_test(abstract_db *db, int argc, char **argv)
{

  printf("Run Micro Benchmark %d %s\n", argc, *argv);

  optind = 1;

  while (1) {
    static struct option long_options[] =
    {
      {"conflict-rate" , required_argument , 0, 'c'},
      {"abort-rate"    , required_argument , 0, 'a'},
      {"read-rate"     , required_argument , 0, 'r'},
      {"txn-length"    , required_argument , 0, 't'},
      {"read-first"    , no_argument       , &read_first , 1}
    };
    int option_index = 0;
    int c = getopt_long(argc, argv, "c:d:r:t:", long_options, &option_index);
    if (c == -1)
      break;

        /* getopt_long stores the option index here. */

      switch (c)
      {
        case 0:
        if (long_options[option_index].flag != 0)
          break;
        abort();
        break;

        case 'c':
        conflict_rate = atof(optarg);
        cout<<"conflict rate "<< conflict_rate <<endl;

        if(conflict_rate == 0)
          break;
        else if(conflict_rate < 1.0/records_per_table)
          conflict_rate = 1.0/records_per_table;
        else if(conflict_rate > 1)
          conflict_rate = 1;
        
        break;

        case 'a':
        user_abort_rate = atof(optarg);
        cout<<"user abort rate "<< read_rate <<endl;

        if(user_abort_rate > 1)
          user_abort_rate = 1;

        break;

        case 'r':
        read_rate = atof(optarg);
        cout<<"read rate "<< read_rate <<endl;

        if(read_rate > 1)
          read_rate = 1;

        break;

        case 't':
        txn_length  = atoi(optarg);    
        cout<<"txn length "<< txn_length<<endl;
        ALWAYS_ASSERT(txn_length > 0);
        break;

        default:
          fprintf(stderr, "Wrong Arg %d\n", c);
          exit(1);
      }
     
  }

  if(conflict_rate > 0)
    access_range = 1 / conflict_rate * nthreads - 1;

  ALWAYS_ASSERT(access_range < records_per_table); 

  fprintf(stderr, "txn length %lu abort rate %f conflict rate %f read rate %f read first %d access_range %lu\n", 
    txn_length, user_abort_rate, conflict_rate, read_rate, read_first, access_range);

  micro_bench_runner r(db);

  r.run();

  print_profile();

}
