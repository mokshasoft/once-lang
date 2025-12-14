/* Linux interpretation - C backend
 *
 * Comprehensive syscall wrappers for Linux.
 * Each once_* function corresponds to a primitive in syscalls.once
 *
 * String Convention:
 * OnceString stores both pointer and length, but the C backend guarantees
 * that strings are ALWAYS null-terminated. This allows direct use with
 * syscalls without malloc/copy overhead. The length is kept for:
 * - Safety (bounds checking)
 * - Binary data that may contain embedded nulls
 * - Efficient substring operations
 */

#define _GNU_SOURCE
#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <signal.h>
#include <time.h>
#include <poll.h>
#include <errno.h>

#ifdef __linux__
#include <sys/random.h>
#endif

#ifndef ONCE_TYPES_DEFINED
#define ONCE_TYPES_DEFINED
typedef struct { const char* data; size_t len; } OnceString;
typedef struct { void* data; size_t len; } OnceBuffer;
#endif

/*========================================================================
 * Process Control
 *========================================================================*/

void* once_exit0(void* x) {
    (void)x;
    exit(0);
    return NULL;
}

void* once_exit(int64_t x) {
    exit((int)x);
    return NULL;
}

int64_t once_getpid(void* x) {
    (void)x;
    return (int64_t)getpid();
}

int64_t once_getppid(void* x) {
    (void)x;
    return (int64_t)getppid();
}

int64_t once_getuid(void* x) {
    (void)x;
    return (int64_t)getuid();
}

int64_t once_geteuid(void* x) {
    (void)x;
    return (int64_t)geteuid();
}

int64_t once_getgid(void* x) {
    (void)x;
    return (int64_t)getgid();
}

int64_t once_getegid(void* x) {
    (void)x;
    return (int64_t)getegid();
}

/*========================================================================
 * File Descriptors
 *========================================================================*/

int64_t once_fd_read(int64_t fd, OnceBuffer buf, int64_t count) {
    ssize_t result = read((int)fd, buf.data, (size_t)count);
    return (int64_t)result;
}

int64_t once_fd_write(int64_t fd, OnceBuffer buf, int64_t count) {
    ssize_t result = write((int)fd, buf.data, (size_t)count);
    return (int64_t)result;
}

int64_t once_fd_close(int64_t fd) {
    return (int64_t)close((int)fd);
}

int64_t once_fd_dup(int64_t fd) {
    return (int64_t)dup((int)fd);
}

int64_t once_fd_dup2(int64_t oldfd, int64_t newfd) {
    return (int64_t)dup2((int)oldfd, (int)newfd);
}

/*========================================================================
 * File Operations
 *
 * Note: All OnceString values are null-terminated by invariant,
 * so we can pass path.data directly to syscalls.
 *========================================================================*/

int64_t once_open(OnceString path, int64_t flags, int64_t mode) {
    return (int64_t)open(path.data, (int)flags, (mode_t)mode);
}

int64_t once_creat(OnceString path, int64_t mode) {
    return (int64_t)creat(path.data, (mode_t)mode);
}

int64_t once_unlink(OnceString path) {
    return (int64_t)unlink(path.data);
}

int64_t once_rename(OnceString oldpath, OnceString newpath) {
    return (int64_t)rename(oldpath.data, newpath.data);
}

int64_t once_symlink(OnceString target, OnceString linkpath) {
    return (int64_t)symlink(target.data, linkpath.data);
}

int64_t once_readlink(OnceString path, OnceBuffer buf, int64_t bufsiz) {
    return (int64_t)readlink(path.data, buf.data, (size_t)bufsiz);
}

int64_t once_stat(OnceString path, OnceBuffer buf) {
    return (int64_t)stat(path.data, (struct stat*)buf.data);
}

int64_t once_lstat(OnceString path, OnceBuffer buf) {
    return (int64_t)lstat(path.data, (struct stat*)buf.data);
}

int64_t once_fstat(int64_t fd, OnceBuffer buf) {
    return (int64_t)fstat((int)fd, (struct stat*)buf.data);
}

int64_t once_chmod(OnceString path, int64_t mode) {
    return (int64_t)chmod(path.data, (mode_t)mode);
}

int64_t once_fchmod(int64_t fd, int64_t mode) {
    return (int64_t)fchmod((int)fd, (mode_t)mode);
}

int64_t once_chown(OnceString path, int64_t owner, int64_t group) {
    return (int64_t)chown(path.data, (uid_t)owner, (gid_t)group);
}

int64_t once_truncate(OnceString path, int64_t length) {
    return (int64_t)truncate(path.data, (off_t)length);
}

int64_t once_ftruncate(int64_t fd, int64_t length) {
    return (int64_t)ftruncate((int)fd, (off_t)length);
}

/*========================================================================
 * Directory Operations
 *========================================================================*/

int64_t once_mkdir(OnceString path, int64_t mode) {
    return (int64_t)mkdir(path.data, (mode_t)mode);
}

int64_t once_rmdir(OnceString path) {
    return (int64_t)rmdir(path.data);
}

int64_t once_chdir(OnceString path) {
    return (int64_t)chdir(path.data);
}

int64_t once_getcwd(OnceBuffer buf, int64_t size) {
    char* result = getcwd(buf.data, (size_t)size);
    return result ? (int64_t)strlen(result) : -1;
}

int64_t once_chroot(OnceString path) {
    return (int64_t)chroot(path.data);
}

/*========================================================================
 * File Seeking
 *========================================================================*/

int64_t once_lseek(int64_t fd, int64_t offset, int64_t whence) {
    return (int64_t)lseek((int)fd, (off_t)offset, (int)whence);
}

/*========================================================================
 * Time
 *========================================================================*/

int64_t once_time(void* x) {
    (void)x;
    return (int64_t)time(NULL);
}

int64_t once_clock_gettime(int64_t clk_id, OnceBuffer buf) {
    return (int64_t)clock_gettime((clockid_t)clk_id, (struct timespec*)buf.data);
}

int64_t once_sleep(int64_t seconds) {
    return (int64_t)sleep((unsigned int)seconds);
}

int64_t once_usleep(int64_t usec) {
    return (int64_t)usleep((useconds_t)usec);
}

int64_t once_nanosleep(OnceBuffer req, OnceBuffer rem) {
    return (int64_t)nanosleep((struct timespec*)req.data, (struct timespec*)rem.data);
}

/*========================================================================
 * Environment
 *========================================================================*/

OnceString once_getenv(OnceString name) {
    char* result = getenv(name.data);
    if (result) {
        return (OnceString){ .data = result, .len = strlen(result) };
    }
    return (OnceString){ .data = NULL, .len = 0 };
}

int64_t once_setenv(OnceString name, OnceString value, int64_t overwrite) {
    return (int64_t)setenv(name.data, value.data, (int)overwrite);
}

int64_t once_unsetenv(OnceString name) {
    return (int64_t)unsetenv(name.data);
}

/*========================================================================
 * Memory Mapping
 *========================================================================*/

OnceBuffer once_mmap(int64_t addr, int64_t length, int64_t prot, int64_t flags, int64_t fd, int64_t offset) {
    void* result = mmap((void*)addr, (size_t)length, (int)prot, (int)flags, (int)fd, (off_t)offset);
    if (result == MAP_FAILED) {
        return (OnceBuffer){ .data = NULL, .len = 0 };
    }
    return (OnceBuffer){ .data = result, .len = (size_t)length };
}

int64_t once_munmap(OnceBuffer buf, int64_t length) {
    return (int64_t)munmap(buf.data, (size_t)length);
}

int64_t once_mprotect(OnceBuffer buf, int64_t length, int64_t prot) {
    return (int64_t)mprotect(buf.data, (size_t)length, (int)prot);
}

/*========================================================================
 * Signals
 *========================================================================*/

int64_t once_kill(int64_t pid, int64_t sig) {
    return (int64_t)kill((pid_t)pid, (int)sig);
}

int64_t once_raise(int64_t sig) {
    return (int64_t)raise((int)sig);
}

int64_t once_pause(void* x) {
    (void)x;
    return (int64_t)pause();
}

/*========================================================================
 * Pipe and IPC
 *========================================================================*/

int64_t once_pipe(OnceBuffer buf) {
    int* fds = (int*)buf.data;
    return (int64_t)pipe(fds);
}

/*========================================================================
 * Socket Operations
 *========================================================================*/

int64_t once_socket(int64_t domain, int64_t type, int64_t protocol) {
    return (int64_t)socket((int)domain, (int)type, (int)protocol);
}

int64_t once_bind(int64_t sockfd, OnceBuffer addr, int64_t addrlen) {
    return (int64_t)bind((int)sockfd, (struct sockaddr*)addr.data, (socklen_t)addrlen);
}

int64_t once_listen(int64_t sockfd, int64_t backlog) {
    return (int64_t)listen((int)sockfd, (int)backlog);
}

int64_t once_accept(int64_t sockfd, OnceBuffer addr, OnceBuffer addrlen) {
    return (int64_t)accept((int)sockfd, (struct sockaddr*)addr.data, (socklen_t*)addrlen.data);
}

int64_t once_connect(int64_t sockfd, OnceBuffer addr, int64_t addrlen) {
    return (int64_t)connect((int)sockfd, (struct sockaddr*)addr.data, (socklen_t)addrlen);
}

int64_t once_send(int64_t sockfd, OnceBuffer buf, int64_t len, int64_t flags) {
    return (int64_t)send((int)sockfd, buf.data, (size_t)len, (int)flags);
}

int64_t once_recv(int64_t sockfd, OnceBuffer buf, int64_t len, int64_t flags) {
    return (int64_t)recv((int)sockfd, buf.data, (size_t)len, (int)flags);
}

int64_t once_shutdown(int64_t sockfd, int64_t how) {
    return (int64_t)shutdown((int)sockfd, (int)how);
}

int64_t once_setsockopt(int64_t sockfd, int64_t level, int64_t optname, OnceBuffer optval, int64_t optlen) {
    return (int64_t)setsockopt((int)sockfd, (int)level, (int)optname, optval.data, (socklen_t)optlen);
}

int64_t once_getsockopt(int64_t sockfd, int64_t level, int64_t optname, OnceBuffer optval, OnceBuffer optlen) {
    return (int64_t)getsockopt((int)sockfd, (int)level, (int)optname, optval.data, (socklen_t*)optlen.data);
}

/*========================================================================
 * Polling
 *========================================================================*/

int64_t once_poll(OnceBuffer fds, int64_t nfds, int64_t timeout) {
    return (int64_t)poll((struct pollfd*)fds.data, (nfds_t)nfds, (int)timeout);
}

/*========================================================================
 * Random
 *========================================================================*/

int64_t once_getrandom(OnceBuffer buf, int64_t buflen, int64_t flags) {
#ifdef __linux__
    return (int64_t)getrandom(buf.data, (size_t)buflen, (unsigned int)flags);
#else
    /* Fallback for non-Linux systems */
    (void)flags;
    arc4random_buf(buf.data, (size_t)buflen);
    return buflen;
#endif
}

/*========================================================================
 * Threading (low-level)
 *========================================================================*/

#define _GNU_SOURCE
#include <sched.h>
#include <linux/futex.h>
#include <sys/syscall.h>

int64_t once_clone(int64_t flags, OnceBuffer stack) {
    /* clone() is complex - it needs assembly to properly set up the new thread.
     * This is a simplified wrapper that uses the clone syscall directly.
     * For proper thread creation, see Thread.c which handles stack setup.
     */
    return (int64_t)syscall(SYS_clone, (unsigned long)flags, stack.data, NULL, NULL, 0);
}

int64_t once_futex(OnceBuffer addr, int64_t op, int64_t val,
                   OnceBuffer timeout, OnceBuffer addr2, int64_t val3) {
    return (int64_t)syscall(SYS_futex,
                            (int*)addr.data,
                            (int)op,
                            (int)val,
                            timeout.data,
                            addr2.data,
                            (int)val3);
}

int64_t once_gettid(void* x) {
    (void)x;
    return (int64_t)syscall(SYS_gettid);
}
