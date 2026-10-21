// icount CMD ARGS...: run CMD and print its user-mode instruction count
// (retired instructions, children included). Unlike wall or CPU time it
// does not depend on the machine's load. Build: gcc -O2 -o icount icount.c
#define _GNU_SOURCE
#include <linux/perf_event.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>
#include <string.h>
#include <stdio.h>
#include <stdint.h>
int main(int argc, char **argv) {
  struct perf_event_attr a; memset(&a, 0, sizeof a);
  a.size = sizeof a; a.type = PERF_TYPE_HARDWARE; a.config = PERF_COUNT_HW_INSTRUCTIONS;
  a.disabled = 1; a.enable_on_exec = 1; a.inherit = 1; a.exclude_kernel = 1; a.exclude_hv = 1;
  if (argc < 2) { fprintf(stderr, "usage: icount CMD ARGS...\n"); return 2; }
  // the child waits on the pipe until the counter is attached
  int go[2];
  if (pipe(go) != 0) { perror("pipe"); return 1; }
  pid_t pid = fork();
  if (pid < 0) { perror("fork"); return 1; }
  if (pid == 0) {
    char c; close(go[1]);
    if (read(go[0], &c, 1) != 1) _exit(126);
    execvp(argv[1], argv + 1); perror("exec"); _exit(127);
  }
  int fd = syscall(SYS_perf_event_open, &a, pid, -1, -1, 0);
  if (fd < 0) { perror("perf_event_open"); return 1; }
  close(go[0]);
  if (write(go[1], "x", 1) != 1) { perror("write"); return 1; }
  close(go[1]);
  int st; waitpid(pid, &st, 0);
  uint64_t n = 0;
  if (read(fd, &n, sizeof n) != sizeof n) { perror("read"); return 1; }
  fprintf(stderr, "instructions %.3f G\n", n / 1e9);
  return WIFEXITED(st) ? WEXITSTATUS(st) : 1;
}
