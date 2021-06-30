# -*- coding: utf-8 -*-

__author__ = 'Shawfy'

from typing import Optional, List, Iterable, Callable
import os
import multiprocessing
import sys
import time
from binascii import hexlify


def cpu_count() -> int:
    """Returns the number of processors on this machine."""
    if multiprocessing is None:
        return 1
    try:
        return multiprocessing.cpu_count()
    except NotImplementedError:
        pass
    try:
        return os.sysconf("SC_NPROCESSORS_CONF")  # type: ignore
    except (AttributeError, ValueError):
        pass
    print("Could not detect number of processors; assuming 1")
    return 1


def _reseed_random() -> None:
    if "random" not in sys.modules:
        return
    import random

    # If os.urandom is available, this method does the same thing as
    # random.seed (at least as of python 2.6).  If os.urandom is not
    # available, we mix in the pid in addition to a timestamp.
    try:
        seed = int(hexlify(os.urandom(16)), 16)
    except NotImplementedError:
        seed = int(time.time() * 1000) ^ os.getpid()
    random.seed(seed)

_task_id = None
def fork_processes(
        num_processes: Optional[int], max_restarts: Optional[int] = None
) -> int:
    """Starts multiple worker processes.

    If ``num_processes`` is None or <= 0, we detect the number of cores
    available on this machine and fork that number of child
    processes. If ``num_processes`` is given and > 0, we fork that
    specific number of sub-processes.

    Since we use processes and not threads, there is no shared memory
    between any server code.

    Note that multiple processes are not compatible with the autoreload
    module (or the ``autoreload=True`` option to `tornado.web.Application`
    which defaults to True when ``debug=True``).
    When using multiple processes, no IOLoops can be created or
    referenced until after the call to ``fork_processes``.

    In each child process, ``fork_processes`` returns its *task id*, a
    number between 0 and ``num_processes``.  Processes that exit
    abnormally (due to a signal or non-zero exit status) are restarted
    with the same id (up to ``max_restarts`` times).  In the parent
    process, ``fork_processes`` calls ``sys.exit(0)`` after all child
    processes have exited normally.

    max_restarts defaults to 100.

    Availability: Unix
    """
    if sys.platform == "win32":
        # The exact form of this condition matters to mypy; it understands
        # if but not assert in this context.
        raise Exception("fork not available on windows")
    if max_restarts is None:
        max_restarts = 100

    global _task_id
    assert _task_id is None
    if num_processes is None or num_processes <= 0:
        num_processes = cpu_count()
    print("Starting %d processes", num_processes)
    children = {}

    def start_child(i: int) -> Optional[int]:
        pid = os.fork()
        if pid == 0:
            # child process
            _reseed_random()
            global _task_id
            _task_id = i
            return i
        else:
            children[pid] = i
            return None

    for i in range(num_processes):
        id = start_child(i)
        if id is not None:
            return id
    num_restarts = 0
    while children:
        pid, status = os.wait()
        if pid not in children:
            continue
        id = children.pop(pid)
        if os.WIFSIGNALED(status):
            print(
                "child %d (pid %d) killed by signal %d, restarting",
                id,
                pid,
                os.WTERMSIG(status),
            )
        elif os.WEXITSTATUS(status) != 0:
            print(
                "child %d (pid %d) exited with status %d, restarting",
                id,
                pid,
                os.WEXITSTATUS(status),
            )
        else:
            print("child %d (pid %d) exited normally", id, pid)
            continue
        num_restarts += 1
        if num_restarts > max_restarts:
            raise RuntimeError("Too many child restarts, giving up")
        new_id = start_child(id)
        if new_id is not None:
            return new_id
    # All child processes exited cleanly, so exit the master process
    # instead of just returning to right after the call to
    # fork_processes (which will probably just start up another IOLoop
    # unless the caller checks the return value).
    sys.exit(0)


import socket
import errno

_DEFAULT_BACKLOG = 128


def errno_from_exception(e: BaseException) -> Optional[int]:
    """Provides the errno from an Exception object.

    There are cases that the errno attribute was not set so we pull
    the errno out of the args but if someone instantiates an Exception
    without any args you will get a tuple error. So this function
    abstracts all that behavior to give you a safe way to get the
    errno.
    """

    if hasattr(e, "errno"):
        return e.errno  # type: ignore
    elif e.args:
        return e.args[0]
    else:
        return None


def bind_sockets(
        port: int,
        address: Optional[str] = None,
        family: socket.AddressFamily = socket.AF_UNSPEC,
        backlog: int = _DEFAULT_BACKLOG,
        flags: Optional[int] = None,
        reuse_port: bool = False,
) -> List[socket.socket]:
    """Creates listening sockets bound to the given port and address.

    Returns a list of socket objects (multiple sockets are returned if
    the given address maps to multiple IP addresses, which is most common
    for mixed IPv4 and IPv6 use).

    Address may be either an IP address or hostname.  If it's a hostname,
    the server will listen on all IP addresses associated with the
    name.  Address may be an empty string or None to listen on all
    available interfaces.  Family may be set to either `socket.AF_INET`
    or `socket.AF_INET6` to restrict to IPv4 or IPv6 addresses, otherwise
    both will be used if available.

    The ``backlog`` argument has the same meaning as for
    `socket.listen() <socket.socket.listen>`.

    ``flags`` is a bitmask of AI_* flags to `~socket.getaddrinfo`, like
    ``socket.AI_PASSIVE | socket.AI_NUMERICHOST``.

    ``reuse_port`` option sets ``SO_REUSEPORT`` option for every socket
    in the list. If your platform doesn't support this option ValueError will
    be raised.
    """
    if reuse_port and not hasattr(socket, "SO_REUSEPORT"):
        raise ValueError("the platform doesn't support SO_REUSEPORT")

    sockets = []
    if address == "":
        address = None
    if not socket.has_ipv6 and family == socket.AF_UNSPEC:
        # Python can be compiled with --disable-ipv6, which causes
        # operations on AF_INET6 sockets to fail, but does not
        # automatically exclude those results from getaddrinfo
        # results.
        # http://bugs.python.org/issue16208
        family = socket.AF_INET
    if flags is None:
        flags = socket.AI_PASSIVE
    bound_port = None
    unique_addresses = set()  # type: set
    for res in sorted(
            socket.getaddrinfo(address, port, family, socket.SOCK_STREAM, 0, flags),
            key=lambda x: x[0],
    ):
        if res in unique_addresses:
            continue

        unique_addresses.add(res)

        af, socktype, proto, canonname, sockaddr = res
        if (
                sys.platform == "darwin"
                and address == "localhost"
                and af == socket.AF_INET6
                and sockaddr[3] != 0
        ):
            # Mac OS X includes a link-local address fe80::1%lo0 in the
            # getaddrinfo results for 'localhost'.  However, the firewall
            # doesn't understand that this is a local address and will
            # prompt for access (often repeatedly, due to an apparent
            # bug in its ability to remember granting access to an
            # application). Skip these addresses.
            continue
        try:
            sock = socket.socket(af, socktype, proto)
        except socket.error as e:
            if errno_from_exception(e) == errno.EAFNOSUPPORT:
                continue
            raise
        if os.name != "nt":
            try:
                sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            except socket.error as e:
                if errno_from_exception(e) != errno.ENOPROTOOPT:
                    # Hurd doesn't support SO_REUSEADDR.
                    raise
        if reuse_port:
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEPORT, 1)
        if af == socket.AF_INET6:
            # On linux, ipv6 sockets accept ipv4 too by default,
            # but this makes it impossible to bind to both
            # 0.0.0.0 in ipv4 and :: in ipv6.  On other systems,
            # separate sockets *must* be used to listen for both ipv4
            # and ipv6.  For consistency, always disable ipv4 on our
            # ipv6 sockets and use a separate ipv4 socket when needed.
            #
            # Python 2.x on windows doesn't have IPPROTO_IPV6.
            if hasattr(socket, "IPPROTO_IPV6"):
                sock.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_V6ONLY, 1)

        # automatic port allocation with port=None
        # should bind on the same port on IPv4 and IPv6
        host, requested_port = sockaddr[:2]
        if requested_port == 0 and bound_port is not None:
            sockaddr = tuple([host, bound_port] + list(sockaddr[2:]))

        sock.setblocking(False)
        try:
            sock.bind(sockaddr)
        except OSError as e:
            if (
                    errno_from_exception(e) == errno.EADDRNOTAVAIL
                    and address == "localhost"
                    and sockaddr[0] == "::1"
            ):
                # On some systems (most notably docker with default
                # configurations), ipv6 is partially disabled:
                # socket.has_ipv6 is true, we can create AF_INET6
                # sockets, and getaddrinfo("localhost", ...,
                # AF_PASSIVE) resolves to ::1, but we get an error
                # when binding.
                #
                # Swallow the error, but only for this specific case.
                # If EADDRNOTAVAIL occurs in other situations, it
                # might be a real problem like a typo in a
                # configuration.
                sock.close()
                continue
            else:
                raise
        bound_port = sock.getsockname()[1]
        sock.listen(backlog)
        sockets.append(sock)
    return sockets


class TCPServer(object):
    def __init__(self) -> None:
        self._sockets = {}  # type: Dict[int, socket.socket]
        self._handlers = {}  # type: Dict[int, Callable[[], None]]
        self._pending_sockets = []  # type: List[socket.socket]
        self._started = False
        self._stopped = False

    def bind(
            self,
            port: int,
            address: Optional[str] = None,
            family: socket.AddressFamily = socket.AF_UNSPEC,
            backlog: int = 128,
            reuse_port: bool = False,
    ) -> None:

        print("bind啦")
        if self._started:
            print("我已启动啦")
            self.add_sockets([None])
        else:
            fork_processes(3, None)
            sockets = bind_sockets(
                port, address=address, family=family, backlog=backlog, reuse_port=reuse_port
            )
            self._pending_sockets.extend(sockets)

    def start(
            self, num_processes: Optional[int] = 1, max_restarts: Optional[int] = None
    ) -> None:
        assert not self._started
        self._started = True

        print(f"fork 后添加socket：{self._pending_sockets}")
        sockets = self._pending_sockets
        self._pending_sockets = []
        print(f"fork 后添加socket2122222：{self._pending_sockets}")
        self.add_sockets(sockets)

    def add_sockets(self, sockets: Iterable[socket.socket]) -> None:
        """Makes this server start accepting connections on the given sockets.

        The ``sockets`` parameter is a list of socket objects such as
        those returned by `~tornado.netutil.bind_sockets`.
        `add_sockets` is typically used in combination with that
        method and `tornado.process.fork_processes` to provide greater
        control over the initialization of a multi-process server.
        """
        for sock in sockets:
            print(sock)

tcp = TCPServer()
tcp.bind(8888, reuse_port=True)
tcp.start(3)