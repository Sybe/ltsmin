/** @file runtime.h
 *  @brief Runtime support library.
 */

#ifndef RUNTIME_H
#define RUNTIME_H

/**
\defgroup runtime Runtime support library.
 */
///@{

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <setjmp.h>
#include <errno.h>
#include <stdint.h>
#include <popt.h>
#include <hre-main.h>

typedef struct {
	char* key;
	int val;
} si_map_entry;

/**
\brief Find the value for a given key, or -1 if it does not exist.
 */
extern int linear_search(const si_map_entry map[],const char*key);

extern char *key_search(si_map_entry map[],const int val);

/**
\brief Parse a string that represents command line options.
 */
extern void RTparseOptions(const char* argline,int *argc_p,const char***argv_p);

#define RTstackBottom HREstackBottom

extern void* RTmalloc(size_t size);

extern void* RTmallocZero(size_t size);

extern void* RTalign(size_t alignment, size_t size);

extern void* RTalignZero(size_t align, size_t size);

extern void* RTrealloc(void *rt_ptr, size_t size);

extern char* RTstrdup(const char *str);

extern void RTfree(void *rt_ptr);

#define RT_NEW(sort) RTmallocZero(sizeof(sort))

extern void *RTdlsym (const char *libname, void *handle, const char *symbol);

/**
\brief Initialize the runtime library using popt.
\param min_args The minimum number of arguments allowed.
\param max_args The maximum number of arguments allowed, where -1 denotes infinite.
*/
extern void RTinitPopt(int *argc_p,char**argv_p[],const struct poptOption * options,
	int min_args,int max_args,char*args[],
	const char* pgm_prefix,const char* arg_help,const char* extra_help
);

/**
\brief Return the next argument.
 */
extern char* RTinitNextArg();


/**
\brief Print usage of tool.
Due to the fact that we may have different extra string for help and usage,
the function poptPrintUsage should not be called directly.
 */
#define RTexitUsage(code) do {HREprintUsage();HREabort(code);} while(0)

/**
\brief Print help of tool.
Due to the fact that we may have different extra string for help and usage,
the function poptPrintHelp should not be called directly.
 */
extern void RTexitHelp(int exit_code);

extern int RTverbosity;

extern void RTinit(int *argc, char **argv[]);
/**< @brief Initializes the runtime library.

Some platform do not like it is you change argv. Thus this
call makes a copy of argv allowing subsequent calls
to make changes to argv without copying again.
*/


extern void (*RThandleFatal)(const char*file,int line,int errnum,int code);

#define Warning(log,...)  HREmessage(log,__VA_ARGS__)
#define WarningCall(log,...) HREmessageCall(log,__VA_ARGS__)
#define Log(log,...) HREmessage(log,__VA_ARGS__)
#define LogCall(log,...) HREmessageCall(log,__VA_ARGS__)
#define Fatal(code,log,...) Abort(__VA_ARGS__)
#define FatalCall(code,log,...) AbortCall(__VA_ARGS__)

/**
\brief Check if an integer is between a minimum and a maximum.
*/
#define RangeCheckInt(val,min,max) if ((val) < (min) || (val) > (max)) \
    Abort("value %d is out of range [%d,%d]",val,min,max)

///@}

/** \defgroup rt_sysinfo Functions for retrieving system information. */
/*@{*/

/// Get the number of CPUs.
extern int RTnumCPUs();

/// Get the amount of memory.
extern size_t RTmemSize();

/// Get the page size.
extern size_t RTpageSize();

/*}@*/

#endif

