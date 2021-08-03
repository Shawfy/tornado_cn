#
# Copyright 2009 Facebook
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may
# not use this file except in compliance with the License. You may obtain
# a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations
# under the License.

"""``tornado.web`` provides a simple web framework with asynchronous
features that allow it to scale to large numbers of open connections,
making it ideal for `long polling
<http://en.wikipedia.org/wiki/Push_technology#Long_polling>`_.

<tornado.web>提供了一个允许大量连接的简单异步web框架，使其成为处理长连接的一种理想选择。

Here is a simple "Hello, world" example app:

.. testcode::

    import tornado.ioloop
    import tornado.web

    class MainHandler(tornado.web.RequestHandler):
        def get(self):
            self.write("Hello, world")

    if __name__ == "__main__":
        application = tornado.web.Application([
            (r"/", MainHandler),
        ])
        application.listen(8888)
        tornado.ioloop.IOLoop.current().start()

.. testoutput::
   :hide:


See the :doc:`guide` for additional information.

Thread-safety notes
-------------------

In general, methods on `RequestHandler` and elsewhere in Tornado are
not thread-safe. In particular, methods such as
`~RequestHandler.write()`, `~RequestHandler.finish()`, and
`~RequestHandler.flush()` must only be called from the main thread. If
you use multiple threads it is important to use `.IOLoop.add_callback`
to transfer control back to the main thread before finishing the
request, or to limit your use of other threads to
`.IOLoop.run_in_executor` and ensure that your callbacks running in
the executor do not refer to Tornado objects.

一般情况，RequestHandler的方法或者Tornado中的方法都不是线程安全。尤其这些方法`~RequestHandler.write()`, `~RequestHandler.finish()`, and
`~RequestHandler.flush()`，必须从主线程调用。如果使用多线程，在结束请求前使用IOLoop.add_callback把控制权交回主线程
或者其他线程限制为IOLoop.run_in_executor并且确保回调没有引用tornado对象

"""

import base64
import binascii
import datetime
import email.utils
import functools
import gzip
import hashlib
import hmac
import http.cookies
from inspect import isclass
from io import BytesIO
import mimetypes
import numbers
import os.path
import re
import sys
import threading
import time
import tornado
import traceback
import types
import urllib.parse
from urllib.parse import urlencode

from tornado.concurrent import Future, future_set_result_unless_cancelled
from tornado import escape
from tornado import gen
from tornado.httpserver import HTTPServer
from tornado import httputil
from tornado import iostream
import tornado.locale
from tornado import locale
from tornado.log import access_log, app_log, gen_log
from tornado import template
from tornado.escape import utf8, _unicode
from tornado.routing import (
    AnyMatches,
    DefaultHostMatches,
    HostMatches,
    ReversibleRouter,
    Rule,
    ReversibleRuleRouter,
    URLSpec,
    _RuleList,
)
from tornado.util import ObjectDict, unicode_type, _websocket_mask

url = URLSpec

from typing import (
    Dict,
    Any,
    Union,
    Optional,
    Awaitable,
    Tuple,
    List,
    Callable,
    Iterable,
    Generator,
    Type,
    cast,
    overload,
)
from types import TracebackType
import typing

if typing.TYPE_CHECKING:
    from typing import Set  # noqa: F401


# The following types are accepted by RequestHandler.set_header
# and related methods.
_HeaderTypes = Union[bytes, unicode_type, int, numbers.Integral, datetime.datetime]

_CookieSecretTypes = Union[str, bytes, Dict[int, str], Dict[int, bytes]]


MIN_SUPPORTED_SIGNED_VALUE_VERSION = 1
"""The oldest signed value version supported by this version of Tornado.

Signed values older than this version cannot be decoded.
这个版本tornado支持的最旧签名版本，比这个值更旧的将不能解码。

.. versionadded:: 3.2.1
"""

MAX_SUPPORTED_SIGNED_VALUE_VERSION = 2
"""The newest signed value version supported by this version of Tornado.

Signed values newer than this version cannot be decoded.

这个版本tornado支持的最新签名版本，比这个值更新的将不能解码。

.. versionadded:: 3.2.1
"""

DEFAULT_SIGNED_VALUE_VERSION = 2
"""The signed value version produced by `.RequestHandler.create_signed_value`.

May be overridden by passing a ``version`` keyword argument.

签名值版本生成方法RequestHandler.create_signed_value，
可通过传递一个 ``version`` 关键字参数复写

.. versionadded:: 3.2.1
"""

DEFAULT_SIGNED_VALUE_MIN_VERSION = 1
"""The oldest signed value accepted by `.RequestHandler.get_secure_cookie`.

May be overridden by passing a ``min_version`` keyword argument.
最旧的签名值能被RequestHandler.get_secure_cookie接受
可通过传递一个 ``min_version`` 关键字参数复写

.. versionadded:: 3.2.1
"""


class _ArgDefaultMarker:
    pass


_ARG_DEFAULT = _ArgDefaultMarker()


class RequestHandler(object):
    """Base class for HTTP request handlers.

    Subclasses must define at least one of the methods defined in the
    "Entry points" section below.

    Applications should not construct `RequestHandler` objects
    directly and subclasses should not override ``__init__`` (override
    `~RequestHandler.initialize` instead).

    Http 请求处理基类。

    子类必须包含以下"Entry points"方法其中一个

    应用不能直接构建RequestHandler并且不应重写__init__(使用RequestHandler.initialize替换)
    """
    # 支持的HTTP请求方法
    SUPPORTED_METHODS = ("GET", "HEAD", "POST", "DELETE", "PATCH", "PUT", "OPTIONS")

    _template_loaders = {}  # type: Dict[str, template.BaseLoader]
    _template_loader_lock = threading.Lock()
    _remove_control_chars_regex = re.compile(r"[\x00-\x08\x0e-\x1f]")

    _stream_request_body = False

    # Will be set in _execute.
    _transforms = None  # type: List[OutputTransform]
    path_args = None  # type: List[str]
    path_kwargs = None  # type: Dict[str, str]

    def __init__(
        self,
        application: "Application",
        request: httputil.HTTPServerRequest,
        **kwargs: Any
    ) -> None:
        super().__init__()

        self.application = application
        self.request = request
        self._headers_written = False
        self._finished = False
        self._auto_finish = True
        self._prepared_future = None
        self.ui = ObjectDict(
            (n, self._ui_method(m)) for n, m in application.ui_methods.items()
        )
        # UIModules are available as both `modules` and `_tt_modules` in the
        # template namespace.  Historically only `modules` was available
        # but could be clobbered by user additions to the namespace.
        # The template {% module %} directive looks in `_tt_modules` to avoid
        # possible conflicts.
        self.ui["_tt_modules"] = _UIModuleNamespace(self, application.ui_modules)
        self.ui["modules"] = self.ui["_tt_modules"]
        self.clear()
        assert self.request.connection is not None
        # TODO: need to add set_close_callback to HTTPConnection interface
        self.request.connection.set_close_callback(  # type: ignore
            self.on_connection_close
        )
        self.initialize(**kwargs)  # type: ignore

    def _initialize(self) -> None:
        pass

    initialize = _initialize  # type: Callable[..., None]
    """Hook for subclass initialization. Called for each request.

    A dictionary passed as the third argument of a ``URLSpec`` will be
    supplied as keyword arguments to ``initialize()``.
    
    子类初始化hook,每个请求都会被调用
    
    作为URLSpec的第三个参数传递的字典，将作为关键字提供给initialize()

    Example::

        class ProfileHandler(RequestHandler):
            def initialize(self, database):
                self.database = database

            def get(self, username):
                ...

        app = Application([
            (r'/user/(.*)', ProfileHandler, dict(database=database)),
            ])
    """

    @property
    def settings(self) -> Dict[str, Any]:
        """An alias for `self.application.settings <Application.settings>`."""
        return self.application.settings

    def _unimplemented_method(self, *args: str, **kwargs: str) -> None:
        raise HTTPError(405)

    head = _unimplemented_method  # type: Callable[..., Optional[Awaitable[None]]]
    get = _unimplemented_method  # type: Callable[..., Optional[Awaitable[None]]]
    post = _unimplemented_method  # type: Callable[..., Optional[Awaitable[None]]]
    delete = _unimplemented_method  # type: Callable[..., Optional[Awaitable[None]]]
    patch = _unimplemented_method  # type: Callable[..., Optional[Awaitable[None]]]
    put = _unimplemented_method  # type: Callable[..., Optional[Awaitable[None]]]
    options = _unimplemented_method  # type: Callable[..., Optional[Awaitable[None]]]

    def prepare(self) -> Optional[Awaitable[None]]:
        """Called at the beginning of a request before  `get`/`post`/etc.

        Override this method to perform common initialization regardless
        of the request method.

        Asynchronous support: Use ``async def`` or decorate this method with
        `.gen.coroutine` to make it asynchronous.
        If this method returns an  ``Awaitable`` execution will not proceed
        until the ``Awaitable`` is done.

        在每个请求前调用，比如`get`/`post`/等，

        重写这个方法，可以执行共同的出刷，而不用考虑灭个请求，

        异步支持：使用 async def 或者gen.coroutine装饰该方法
        如果方法返回一个可等待对象（Awaitable），默认会等待对象完成。

        .. versionadded:: 3.1
           Asynchronous support.
        """
        pass

    def on_finish(self) -> None:
        """Called after the end of a request.

        Override this method to perform cleanup, logging, etc.
        This method is a counterpart to `prepare`.  ``on_finish`` may
        not produce any output, as it is called after the response
        has been sent to the client.

        在请求结束后调用

        重写这个方法执行清理，打些日志等
        这个方法与prepare相对，这个方法可能不会有任何输出，因为它被调用是在请求送回客户端之后
        """
        pass

    def on_connection_close(self) -> None:
        """Called in async handlers if the client closed the connection.

        Override this to clean up resources associated with
        long-lived connections.  Note that this method is called only if
        the connection was closed during asynchronous processing; if you
        need to do cleanup after every request override `on_finish`
        instead.

        Proxies may keep a connection open for a time (perhaps
        indefinitely) after the client has gone away, so this method
        may not be called promptly after the end user closes their
        connection.

        此方法在异步处理中且客户端连接关闭会被执行

        重写此方法清除与长连接相关的资源，注意，只有这个连接在异步处理中被关闭，才会调用此方法，
        如果需要在每个请求后做些清理就重写此方法

        客户端断开后，代理会保持连接一段时间（也有可能是无限期），客户端关闭连接后，此方法可能不会立即执行

        """
        if _has_stream_request_body(self.__class__):
            if not self.request._body_future.done():
                self.request._body_future.set_exception(iostream.StreamClosedError())
                self.request._body_future.exception()

    def clear(self) -> None:
        """Resets all headers and content for this response.
           重置所有响应的请求头和内容
        """
        self._headers = httputil.HTTPHeaders(
            {
                "Server": "TornadoServer/%s" % tornado.version,
                "Content-Type": "text/html; charset=UTF-8",
                "Date": httputil.format_timestamp(time.time()),
            }
        )
        self.set_default_headers()
        self._write_buffer = []  # type: List[bytes]
        self._status_code = 200
        self._reason = httputil.responses[200]

    def set_default_headers(self) -> None:
        """Override this to set HTTP headers at the beginning of the request.

        For example, this is the place to set a custom ``Server`` header.
        Note that setting such headers in the normal flow of request
        processing may not do what you want, since headers may be reset
        during error handling.

        重写这个方法可在请求开始时设置请求头

        例如，在这里设置一个自定义的server头，但是需要注意，请求过程中可能不会实现设置的请求头，
        因为请求头可能在错误处理中被重置
        """
        pass

    def set_status(self, status_code: int, reason: Optional[str] = None) -> None:
        """Sets the status code for our response.

        http请求返回响应的状态码

        :arg int status_code: Response status code.
        :arg str reason: Human-readable reason phrase describing the status
            code. If ``None``, it will be filled in from
            `http.client.responses` or "Unknown".
            用人们易读的语言描述状态码，如果是None,将会用http.client.responses填充或者unknown

        .. versionchanged:: 5.0

           No longer validates that the response code is in
           `http.client.responses`.
        """
        self._status_code = status_code
        if reason is not None:
            self._reason = escape.native_str(reason)
        else:
            self._reason = httputil.responses.get(status_code, "Unknown")

    def get_status(self) -> int:
        """Returns the status code for our response."""
        """获得HTTP响应状态码"""
        return self._status_code

    def set_header(self, name: str, value: _HeaderTypes) -> None:
        """Sets the given response header name and value.
        设置响应头

        All header values are converted to strings (`datetime` objects
        are formatted according to the HTTP specification for the
        ``Date`` header).
        所有头部值都被转字符串类型（datetime对象会根据http的日期头规范格式化）
        """
        self._headers[name] = self._convert_header_value(value)

    def add_header(self, name: str, value: _HeaderTypes) -> None:
        """Adds the given response header and value.
        添加响应头

        Unlike `set_header`, `add_header` may be called multiple times
        to return multiple values for the same header.
        和`set_header`不同，`add_header` 相同的头多次调用会返回多个值，多个值会拼接在一起。
        """
        self._headers.add(name, self._convert_header_value(value))

    def clear_header(self, name: str) -> None:
        """Clears an outgoing header, undoing a previous `set_header` call.
        清除输出头，取消之前的`set_header`调用

        Note that this method does not apply to multi-valued headers
        set by `add_header`.
        *忽略上面英文提示，add_header设置的值也会被删除
        """
        if name in self._headers:
            del self._headers[name]

    _INVALID_HEADER_CHAR_RE = re.compile(r"[\x00-\x1f]")
    # 特殊字符正则

    def _convert_header_value(self, value: _HeaderTypes) -> str:
        # Convert the input value to a str. This type check is a bit
        # subtle: The bytes case only executes on python 3, and the
        # unicode case only executes on python 2, because the other
        # cases are covered by the first match for str.
        """头部各类型参数值转为str，特殊字符或特殊类型会抛出异常"""
        if isinstance(value, str):
            retval = value
        elif isinstance(value, bytes):  # py3
            # Non-ascii characters in headers are not well supported,
            # but if you pass bytes, use latin1 so they pass through as-is.
            retval = value.decode("latin1")
        elif isinstance(value, unicode_type):  # py2
            # TODO: This is inconsistent with the use of latin1 above,
            # but it's been that way for a long time. Should it change?
            retval = escape.utf8(value)
        elif isinstance(value, numbers.Integral):
            # return immediately since we know the converted value will be safe
            return str(value)
        elif isinstance(value, datetime.datetime):
            return httputil.format_timestamp(value)
        else:
            raise TypeError("Unsupported header value %r" % value)
        # If \n is allowed into the header, it is possible to inject
        # additional headers or split the request.
        if RequestHandler._INVALID_HEADER_CHAR_RE.search(retval):
            raise ValueError("Unsafe header value %r", retval)
        return retval

    @overload
    def get_argument(self, name: str, default: str, strip: bool = True) -> str:
        pass

    @overload
    def get_argument(  # noqa: F811
        self, name: str, default: _ArgDefaultMarker = _ARG_DEFAULT, strip: bool = True
    ) -> str:
        pass

    @overload
    def get_argument(  # noqa: F811
        self, name: str, default: None, strip: bool = True
    ) -> Optional[str]:
        pass

    def get_argument(  # noqa: F811
        self,
        name: str,
        default: Union[None, str, _ArgDefaultMarker] = _ARG_DEFAULT,
        strip: bool = True,
    ) -> Optional[str]:
        """Returns the value of the argument with the given name.
        根据给定名称获得请求的参数，默认会去掉参数前后空格

        If default is not provided, the argument is considered to be
        required, and we raise a `MissingArgumentError` if it is missing.

        如果没有提供默认值，且参数也未找到，默认会抛出`MissingArgumentError`错误

        If the argument appears in the request more than once, we return the
        last value.

        如果参数在request上有多次，默认返回最后一个参数

        This method searches both the query and body arguments.

        这个方法会查找query和body两个地方的参数
        """
        return self._get_argument(name, default, self.request.arguments, strip)

    def get_arguments(self, name: str, strip: bool = True) -> List[str]:
        """Returns a list of the arguments with the given name.
        返回指定名称的参数列表，默认会去掉参数前后空格

        If the argument is not present, returns an empty list.
        如果参数不存在，返回空列表

        This method searches both the query and body arguments.
        这个方法会查找query和body两个地方的参数
        """

        # Make sure `get_arguments` isn't accidentally being called with a
        # positional argument that's assumed to be a default (like in
        # `get_argument`.)
        assert isinstance(strip, bool)

        return self._get_arguments(name, self.request.arguments, strip)

    def get_body_argument(
        self,
        name: str,
        default: Union[None, str, _ArgDefaultMarker] = _ARG_DEFAULT,
        strip: bool = True,
    ) -> Optional[str]:
        """Returns the value of the argument with the given name
        from the request body.
        获得指定名称在request body里的参数，默认会去掉参数前后空格

        If default is not provided, the argument is considered to be
        required, and we raise a `MissingArgumentError` if it is missing.
        如果没有提供默认值，且参数也未找到，默认会抛出`MissingArgumentError`错误

        If the argument appears in the url more than once, we return the
        last value.
        如果参数在url上有多次，默认返回最后一个参数
        .. versionadded:: 3.2
        """
        return self._get_argument(name, default, self.request.body_arguments, strip)

    def get_body_arguments(self, name: str, strip: bool = True) -> List[str]:
        """Returns a list of the body arguments with the given name.
        获得指定名称在request body里的参数列表，默认会去掉参数前后空格

        If the argument is not present, returns an empty list.
        如果参数不存在，返回空列表

        .. versionadded:: 3.2
        """
        return self._get_arguments(name, self.request.body_arguments, strip)

    def get_query_argument(
        self,
        name: str,
        default: Union[None, str, _ArgDefaultMarker] = _ARG_DEFAULT,
        strip: bool = True,
    ) -> Optional[str]:
        """Returns the value of the argument with the given name
        from the request query string.
        获得指定名称在request query里的参数，默认会去掉参数前后空格

        If default is not provided, the argument is considered to be
        required, and we raise a `MissingArgumentError` if it is missing.
        如果没有提供默认值，且参数也未找到，默认会抛出`MissingArgumentError`错误

        If the argument appears in the url more than once, we return the
        last value.
        如果参数在url上有多次，默认返回最后一个参数
        .. versionadded:: 3.2
        """
        return self._get_argument(name, default, self.request.query_arguments, strip)

    def get_query_arguments(self, name: str, strip: bool = True) -> List[str]:
        """Returns a list of the query arguments with the given name.
        获得指定名称在request query里的参数列表，默认会去掉参数前后空格
        If the argument is not present, returns an empty list.
        如果参数不存在，返回空列表
        .. versionadded:: 3.2
        """
        return self._get_arguments(name, self.request.query_arguments, strip)

    def _get_argument(
        self,
        name: str,
        default: Union[None, str, _ArgDefaultMarker],
        source: Dict[str, List[bytes]],
        strip: bool = True,
    ) -> Optional[str]:
        """同 get_argument"""
        args = self._get_arguments(name, source, strip=strip)
        if not args:
            if isinstance(default, _ArgDefaultMarker):
                raise MissingArgumentError(name)
            return default
        return args[-1]

    def _get_arguments(
        self, name: str, source: Dict[str, List[bytes]], strip: bool = True
    ) -> List[str]:
        """同 get_arguments"""
        values = []
        for v in source.get(name, []):
            s = self.decode_argument(v, name=name)
            if isinstance(s, unicode_type):
                # Get rid of any weird control chars (unless decoding gave
                # us bytes, in which case leave it alone)
                s = RequestHandler._remove_control_chars_regex.sub(" ", s)
            if strip:
                s = s.strip()
            values.append(s)
        return values

    def decode_argument(self, value: bytes, name: Optional[str] = None) -> str:
        """Decodes an argument from the request.
        从请求中解码一个参数。

        The argument has been percent-decoded and is now a byte string.
        By default, this method decodes the argument as utf-8 and returns
        a unicode string, but this may be overridden in subclasses.
        这个参数已经被解码现在是一个字节字符串，默认情况，这个方法会将参数解码未utf-8并且
        返回一个unicode字符串，但是它可以被子类重写

        This method is used as a filter for both `get_argument()` and for
        values extracted from the url and passed to `get()`/`post()`/etc.
        此方法可作为过滤器用在`get_argument()`方法，也可用在url中取值并传
        递给`get()`/`post()`方法等

        The name of the argument is provided if known, but may be None
        (e.g. for unnamed groups in the url regex).

        """
        try:
            return _unicode(value)
        except UnicodeDecodeError:
            raise HTTPError(
                400, "Invalid unicode in %s: %r" % (name or "url", value[:40])
            )

    @property
    def cookies(self) -> Dict[str, http.cookies.Morsel]:
        """An alias for
        `self.request.cookies <.httputil.HTTPServerRequest.cookies>`.
        此方法把self.request.cookies包装成此类的一个属性
        """
        return self.request.cookies

    def get_cookie(self, name: str, default: Optional[str] = None) -> Optional[str]:
        """Returns the value of the request cookie with the given name.
        获得指定名称的cookie值

        If the named cookie is not present, returns ``default``.
        如果名称未找到返回默认值

        This method only returns cookies that were present in the request.
        It does not see the outgoing cookies set by `set_cookie` in this
        handler.

        此方法仅返回在当前请求中的cookie值。看不见通过`set_cookie`方法设置的输出cookie值
        """
        if self.request.cookies is not None and name in self.request.cookies:
            return self.request.cookies[name].value
        return default

    def set_cookie(
        self,
        name: str,
        value: Union[str, bytes],
        domain: Optional[str] = None,
        expires: Optional[Union[float, Tuple, datetime.datetime]] = None,
        path: str = "/",
        expires_days: Optional[float] = None,
        **kwargs: Any
    ) -> None:
        """Sets an outgoing cookie name/value with the given options.
        设置输出cookie值和其他选项

        Newly-set cookies are not immediately visible via `get_cookie`;
        they are not present until the next request.
        新设的cookie值不能立即在`get_cookie`方法中获得，需要在下次请求才能获得

        expires may be a numeric timestamp as returned by `time.time`,
        a time tuple as returned by `time.gmtime`, or a
        `datetime.datetime` object.
        过期时间可以是一个数字的时间戳(by `time.time`)、一个tuple类型的格林威治时间（by time.gmtime）
        或者一个`datetime.datetime`对象

        Additional keyword arguments are set on the cookies.Morsel
        directly.
        See https://docs.python.org/3/library/http.cookies.html#http.cookies.Morsel
        for available attributes.
        其他的参数直接在`cookies.Morsel`设置
        其他属性查看https://docs.python.org/3/library/http.cookies.html#http.cookies.Morsel
        """
        # The cookie library only accepts type str, in both python 2 and 3
        name = escape.native_str(name)
        value = escape.native_str(value)
        if re.search(r"[\x00-\x20]", name + value):
            # Don't let us accidentally inject bad stuff
            raise ValueError("Invalid cookie %r: %r" % (name, value))
        if not hasattr(self, "_new_cookie"):
            self._new_cookie = (
                http.cookies.SimpleCookie()
            )  # type: http.cookies.SimpleCookie
        if name in self._new_cookie:
            del self._new_cookie[name]
        self._new_cookie[name] = value
        morsel = self._new_cookie[name]
        if domain:
            morsel["domain"] = domain
        if expires_days is not None and not expires:
            expires = datetime.datetime.utcnow() + datetime.timedelta(days=expires_days)
        if expires:
            morsel["expires"] = httputil.format_timestamp(expires)
        if path:
            morsel["path"] = path
        for k, v in kwargs.items():
            if k == "max_age":
                k = "max-age"

            # skip falsy values for httponly and secure flags because
            # SimpleCookie sets them regardless
            if k in ["httponly", "secure"] and not v:
                continue

            morsel[k] = v

    def clear_cookie(
        self, name: str, path: str = "/", domain: Optional[str] = None
    ) -> None:
        """Deletes the cookie with the given name.
        删除指定名称的cookie

        Due to limitations of the cookie protocol, you must pass the same
        path and domain to clear a cookie as were used when that cookie
        was set (but there is no way to find out on the server side
        which values were used for a given cookie).
        受cookie协议限制，必须使用设置cookie时相同的路径和域去清除cookie(但是无法从
        服务器中找出使用cookie的值)

        Similar to `set_cookie`, the effect of this method will not be
        seen until the following request.
        类似`set_cookie`,此方法在下个请求前看不见效果
        """
        expires = datetime.datetime.utcnow() - datetime.timedelta(days=365)
        self.set_cookie(name, value="", path=path, expires=expires, domain=domain)

    def clear_all_cookies(self, path: str = "/", domain: Optional[str] = None) -> None:
        """Deletes all the cookies the user sent with this request.
        删除用户在本次请求中所有的cookie,调用`clear_cookie`方法做实际的清除

        See `clear_cookie` for more information on the path and domain
        parameters.

        Similar to `set_cookie`, the effect of this method will not be
        seen until the following request.

        .. versionchanged:: 3.2

           Added the ``path`` and ``domain`` parameters.
        """
        for name in self.request.cookies:
            self.clear_cookie(name, path=path, domain=domain)

    def set_secure_cookie(
        self,
        name: str,
        value: Union[str, bytes],
        expires_days: Optional[float] = 30,
        version: Optional[int] = None,
        **kwargs: Any
    ) -> None:
        """Signs and timestamps a cookie so it cannot be forged.
        给cookie加上签名和时间戳防止伪造

        You must specify the ``cookie_secret`` setting in your Application
        to use this method. It should be a long, random sequence of bytes
        to be used as the HMAC secret for the signature.
        必须在应用设置中定义`cookie_secret`，签名应使用一个长且随机的字节序列HMAC密钥

        To read a cookie set with this method, use `get_secure_cookie()`.
        使用`get_secure_cookie()`方法来读取当前方法设置的cookie

        Note that the ``expires_days`` parameter sets the lifetime of the
        cookie in the browser, but is independent of the ``max_age_days``
        parameter to `get_secure_cookie`.
        A value of None limits the lifetime to the current browser session.
        注意`expires_days`参数，它是用来设置cookie在浏览器中的生命周期，但是与
        `get_secure_cookie`中的参数`max_age_days`相互独立

        Secure cookies may contain arbitrary byte values, not just unicode
        strings (unlike regular cookies)
        安全cookie可能包含任意字节值，不仅仅是unicode字符串

        Similar to `set_cookie`, the effect of this method will not be
        seen until the following request.
        和`set_cookie`一样，此方法的效果要在下一个请求中才能看见

        .. versionchanged:: 3.2.1

           Added the ``version`` argument.  Introduced cookie version 2
           and made it the default.
           增加零零版本参数，版本2是cookie默认模式
        """
        self.set_cookie(
            name,
            self.create_signed_value(name, value, version=version),
            expires_days=expires_days,
            **kwargs
        )

    def create_signed_value(
        self, name: str, value: Union[str, bytes], version: Optional[int] = None
    ) -> bytes:
        """Signs and timestamps a string so it cannot be forged.
        创建用签名和时间戳的字符串，防止被伪造

        Normally used via set_secure_cookie, but provided as a separate
        method for non-cookie uses.  To decode a value not stored
        as a cookie use the optional value argument to get_secure_cookie.
        此方法通常通过set_secure_cookie使用，对于不使用cookie可作为独立的方法提供，
        为解码不作为cookie存储的值，可在get_secure_cookie中使用value参数

        .. versionchanged:: 3.2.1

           Added the ``version`` argument.  Introduced cookie version 2
           and made it the default.
        """
        self.require_setting("cookie_secret", "secure cookies")
        secret = self.application.settings["cookie_secret"]
        key_version = None
        if isinstance(secret, dict):
            if self.application.settings.get("key_version") is None:
                raise Exception("key_version setting must be used for secret_key dicts")
            key_version = self.application.settings["key_version"]

        return create_signed_value(
            secret, name, value, version=version, key_version=key_version
        )

    def get_secure_cookie(
        self,
        name: str,
        value: Optional[str] = None,
        max_age_days: float = 31,
        min_version: Optional[int] = None,
    ) -> Optional[bytes]:
        """Returns the given signed cookie if it validates, or None.
        如果签名的cookie有效就返回，否则返回None.

        The decoded cookie value is returned as a byte string (unlike
        `get_cookie`).
        解码的cookie值作为字节字符串返回，和`get_cookie`不同

        Similar to `get_cookie`, this method only returns cookies that
        were present in the request. It does not see outgoing cookies set by
        `set_secure_cookie` in this handler.
        和`get_cookie`一样，这个方法返回的是当前请求中的cookie，不能看见`set_secure_cookie`
        方法设置的cookie

        .. versionchanged:: 3.2.1

           Added the ``min_version`` argument.  Introduced cookie version 2;
           both versions 1 and 2 are accepted by default.
        """
        self.require_setting("cookie_secret", "secure cookies")
        if value is None:
            value = self.get_cookie(name)
        return decode_signed_value(
            self.application.settings["cookie_secret"],
            name,
            value,
            max_age_days=max_age_days,
            min_version=min_version,
        )

    def get_secure_cookie_key_version(
        self, name: str, value: Optional[str] = None
    ) -> Optional[int]:
        """Returns the signing key version of the secure cookie.
        获得安全cookie签名的版本

        The version is returned as int.
        返回的版本是整型数字
        """
        self.require_setting("cookie_secret", "secure cookies")
        if value is None:
            value = self.get_cookie(name)
        if value is None:
            return None
        return get_signature_key_version(value)

    def redirect(
        self, url: str, permanent: bool = False, status: Optional[int] = None
    ) -> None:
        """Sends a redirect to the given (optionally relative) URL.
        重定向url(可选相对路径)

        If the ``status`` argument is specified, that value is used as the
        HTTP status code; otherwise either 301 (permanent) or 302
        (temporary) is chosen based on the ``permanent`` argument.
        The default is 302 (temporary).
        如果`status`已指定，这个值将作为http的状态码，否则将通过`permanent`参数选择301(永久)
        或302(临时)，默认是302
        """
        if self._headers_written:
            raise Exception("Cannot redirect after headers have been written")
        if status is None:
            status = 301 if permanent else 302
        else:
            assert isinstance(status, int) and 300 <= status <= 399
        self.set_status(status)
        self.set_header("Location", utf8(url))
        self.finish()

    def write(self, chunk: Union[str, bytes, dict]) -> None:
        """Writes the given chunk to the output buffer.
        把http返回的数据写入到一个输出buffer中

        To write the output to the network, use the `flush()` method below.
        需要写到网络中，使用flush()

        If the given chunk is a dictionary, we write it as JSON and set
        the Content-Type of the response to be ``application/json``.
        (if you want to send JSON as a different ``Content-Type``, call
        ``set_header`` *after* calling ``write()``).
        如果给的数据是字典，返回时会默认把`Content-Type`设置为`application/json`.
        （如果想发送json数据，且想用其他`Content-Type`类型，可以在调用此方法前，
        调用set_header）

        Note that lists are not converted to JSON because of a potential
        cross-site security vulnerability.  All JSON output should be
        wrapped in a dictionary.  More details at
        http://haacked.com/archive/2009/06/25/json-hijacking.aspx/ and
        https://github.com/facebook/tornado/issues/1009
        注意一个列表不能转为json，因为存在潜在的跨域安全漏洞，所有JSON输出都应包含在
        一个字典里，
        更多细节参看
        http://haacked.com/archive/2009/06/25/json-hijacking.aspx/
        和
        https://github.com/facebook/tornado/issues/1009
        """
        if self._finished:
            raise RuntimeError("Cannot write() after finish()")
        if not isinstance(chunk, (bytes, unicode_type, dict)):
            message = "write() only accepts bytes, unicode, and dict objects"
            if isinstance(chunk, list):
                message += (
                    ". Lists not accepted for security reasons; see "
                    + "http://www.tornadoweb.org/en/stable/web.html#tornado.web.RequestHandler.write"  # noqa: E501
                )
            raise TypeError(message)
        if isinstance(chunk, dict):
            chunk = escape.json_encode(chunk)
            self.set_header("Content-Type", "application/json; charset=UTF-8")
        chunk = utf8(chunk)
        self._write_buffer.append(chunk)

    def render(self, template_name: str, **kwargs: Any) -> "Future[None]":
        """Renders the template with the given arguments as the response.
        根据模板名称返回模板

        ``render()`` calls ``finish()``, so no other output methods can be called
        after it.
        此方法直接调用的finish方法，所有之后没有其他输出方法可以调用

        Returns a `.Future` with the same semantics as the one returned by `finish`.
        Awaiting this `.Future` is optional.
        返回的是finish的可等待Future

        .. versionchanged:: 5.1

           Now returns a `.Future` instead of ``None``.
        """
        if self._finished:
            raise RuntimeError("Cannot render() after finish()")
        html = self.render_string(template_name, **kwargs)

        # Insert the additional JS and CSS added by the modules on the page
        js_embed = []
        js_files = []
        css_embed = []
        css_files = []
        html_heads = []
        html_bodies = []
        for module in getattr(self, "_active_modules", {}).values():
            embed_part = module.embedded_javascript()
            if embed_part:
                js_embed.append(utf8(embed_part))
            file_part = module.javascript_files()
            if file_part:
                if isinstance(file_part, (unicode_type, bytes)):
                    js_files.append(_unicode(file_part))
                else:
                    js_files.extend(file_part)
            embed_part = module.embedded_css()
            if embed_part:
                css_embed.append(utf8(embed_part))
            file_part = module.css_files()
            if file_part:
                if isinstance(file_part, (unicode_type, bytes)):
                    css_files.append(_unicode(file_part))
                else:
                    css_files.extend(file_part)
            head_part = module.html_head()
            if head_part:
                html_heads.append(utf8(head_part))
            body_part = module.html_body()
            if body_part:
                html_bodies.append(utf8(body_part))

        if js_files:
            # Maintain order of JavaScript files given by modules
            js = self.render_linked_js(js_files)
            sloc = html.rindex(b"</body>")
            html = html[:sloc] + utf8(js) + b"\n" + html[sloc:]
        if js_embed:
            js_bytes = self.render_embed_js(js_embed)
            sloc = html.rindex(b"</body>")
            html = html[:sloc] + js_bytes + b"\n" + html[sloc:]
        if css_files:
            css = self.render_linked_css(css_files)
            hloc = html.index(b"</head>")
            html = html[:hloc] + utf8(css) + b"\n" + html[hloc:]
        if css_embed:
            css_bytes = self.render_embed_css(css_embed)
            hloc = html.index(b"</head>")
            html = html[:hloc] + css_bytes + b"\n" + html[hloc:]
        if html_heads:
            hloc = html.index(b"</head>")
            html = html[:hloc] + b"".join(html_heads) + b"\n" + html[hloc:]
        if html_bodies:
            hloc = html.index(b"</body>")
            html = html[:hloc] + b"".join(html_bodies) + b"\n" + html[hloc:]
        return self.finish(html)

    def render_linked_js(self, js_files: Iterable[str]) -> str:
        """Default method used to render the final js links for the
        rendered webpage.
        此方法用于生成网页js links

        Override this method in a sub-classed controller to change the output.
        重写此方法改变输出结果
        """
        paths = []
        unique_paths = set()  # type: Set[str]

        for path in js_files:
            if not is_absolute(path):
                path = self.static_url(path)
            if path not in unique_paths:
                paths.append(path)
                unique_paths.add(path)

        return "".join(
            '<script src="'
            + escape.xhtml_escape(p)
            + '" type="text/javascript"></script>'
            for p in paths
        )

    def render_embed_js(self, js_embed: Iterable[bytes]) -> bytes:
        """Default method used to render the final embedded js for the
        rendered webpage.
        次方法用于嵌入js代码

        Override this method in a sub-classed controller to change the output.
        重写此方法改变输出
        """
        return (
            b'<script type="text/javascript">\n//<![CDATA[\n'
            + b"\n".join(js_embed)
            + b"\n//]]>\n</script>"
        )

    def render_linked_css(self, css_files: Iterable[str]) -> str:
        """Default method used to render the final css links for the
        rendered webpage.
        此方法用于生成网页css links
        Override this method in a sub-classed controller to change the output.
        重写此方法改变输出
        """
        paths = []
        unique_paths = set()  # type: Set[str]

        for path in css_files:
            if not is_absolute(path):
                path = self.static_url(path)
            if path not in unique_paths:
                paths.append(path)
                unique_paths.add(path)

        return "".join(
            '<link href="' + escape.xhtml_escape(p) + '" '
            'type="text/css" rel="stylesheet"/>'
            for p in paths
        )

    def render_embed_css(self, css_embed: Iterable[bytes]) -> bytes:
        """Default method used to render the final embedded css for the
        rendered webpage.
        次方法用于嵌入css代码

        Override this method in a sub-classed controller to change the output.
        重写此方法改变输出
        """
        return b'<style type="text/css">\n' + b"\n".join(css_embed) + b"\n</style>"

    def render_string(self, template_name: str, **kwargs: Any) -> bytes:
        """Generate the given template with the given arguments.
        使用给定的参数生成指定的模板

        We return the generated byte string (in utf8). To generate and
        write a template as a response, use render() above.
        我们返回生成的字节字符串(utf8).生成一个模板作为响应，使用上面的render()
        """
        # If no template_path is specified, use the path of the calling file
        template_path = self.get_template_path()
        if not template_path:
            frame = sys._getframe(0)
            web_file = frame.f_code.co_filename
            while frame.f_code.co_filename == web_file:
                frame = frame.f_back
            assert frame.f_code.co_filename is not None
            template_path = os.path.dirname(frame.f_code.co_filename)
        with RequestHandler._template_loader_lock:
            if template_path not in RequestHandler._template_loaders:
                loader = self.create_template_loader(template_path)
                RequestHandler._template_loaders[template_path] = loader
            else:
                loader = RequestHandler._template_loaders[template_path]
        t = loader.load(template_name)
        namespace = self.get_template_namespace()
        namespace.update(kwargs)
        return t.generate(**namespace)

    def get_template_namespace(self) -> Dict[str, Any]:
        """Returns a dictionary to be used as the default template namespace.
        返回一个字典用着默认的模板命名空间

        May be overridden by subclasses to add or modify values.
        可以在子类重写来添加或修改值

        The results of this method will be combined with additional
        defaults in the `tornado.template` module and keyword arguments
        to `render` or `render_string`.
        这个方法的结果将会和`tornado.template`和`render`、`render_string`结合
        """
        namespace = dict(
            handler=self,
            request=self.request,
            current_user=self.current_user,
            locale=self.locale,
            _=self.locale.translate,
            pgettext=self.locale.pgettext,
            static_url=self.static_url,
            xsrf_form_html=self.xsrf_form_html,
            reverse_url=self.reverse_url,
        )
        namespace.update(self.ui)
        return namespace

    def create_template_loader(self, template_path: str) -> template.BaseLoader:
        """Returns a new template loader for the given path.
        根据给定路径返回新的模板装载器

        May be overridden by subclasses.  By default returns a
        directory-based loader on the given path, using the
        ``autoescape`` and ``template_whitespace`` application
        settings.  If a ``template_loader`` application setting is
        supplied, uses that instead.
        可以在子类重写，默认根据给丁的路径返回基于目录的装载器，如果application设置了template_loader
        ，它会替换应用设置中的`autoescape`和`template_whitespace`
        """
        settings = self.application.settings
        if "template_loader" in settings:
            return settings["template_loader"]
        kwargs = {}
        if "autoescape" in settings:
            # autoescape=None means "no escaping", so we have to be sure
            # to only pass this kwarg if the user asked for it.
            kwargs["autoescape"] = settings["autoescape"]
        if "template_whitespace" in settings:
            kwargs["whitespace"] = settings["template_whitespace"]
        return template.Loader(template_path, **kwargs)

    def flush(self, include_footers: bool = False) -> "Future[None]":
        """Flushes the current output buffer to the network.
        将当前输出buffer写到网络中

        .. versionchanged:: 4.0
           Now returns a `.Future` if no callback is given.

        .. versionchanged:: 6.0

           The ``callback`` argument was removed.
        """
        assert self.request.connection is not None
        chunk = b"".join(self._write_buffer)
        self._write_buffer = []
        if not self._headers_written:
            self._headers_written = True
            for transform in self._transforms:
                assert chunk is not None
                (
                    self._status_code,
                    self._headers,
                    chunk,
                ) = transform.transform_first_chunk(
                    self._status_code, self._headers, chunk, include_footers
                )
            # Ignore the chunk and only write the headers for HEAD requests
            if self.request.method == "HEAD":
                chunk = b""

            # Finalize the cookie headers (which have been stored in a side
            # object so an outgoing cookie could be overwritten before it
            # is sent).
            if hasattr(self, "_new_cookie"):
                for cookie in self._new_cookie.values():
                    self.add_header("Set-Cookie", cookie.OutputString(None))

            start_line = httputil.ResponseStartLine("", self._status_code, self._reason)
            return self.request.connection.write_headers(
                start_line, self._headers, chunk
            )
        else:
            for transform in self._transforms:
                chunk = transform.transform_chunk(chunk, include_footers)
            # Ignore the chunk and only write the headers for HEAD requests
            if self.request.method != "HEAD":
                return self.request.connection.write(chunk)
            else:
                future = Future()  # type: Future[None]
                future.set_result(None)
                return future

    def finish(self, chunk: Optional[Union[str, bytes, dict]] = None) -> "Future[None]":
        """Finishes this response, ending the HTTP request.
        完成响应，结束当前http请求

        Passing a ``chunk`` to ``finish()`` is equivalent to passing that
        chunk to ``write()`` and then calling ``finish()`` with no arguments.
        调用finish()带chunk参数等价于调用write带chunk和finish不带参数

        Returns a `.Future` which may optionally be awaited to track the sending
        of the response to the client. This `.Future` resolves when all the response
        data has been sent, and raises an error if the connection is closed before all
        data can be sent.
        返回一个`Future`，可以选择等待它来跟踪向客户端发送响应的过程.
        当所有响应数据都已发送时，`.Future`会解决此问题,如果在发送所有数据之前关闭连接，则会引发错误
        .. versionchanged:: 5.1

           Now returns a `.Future` instead of ``None``.
        """
        if self._finished:
            raise RuntimeError("finish() called twice")

        if chunk is not None:
            self.write(chunk)

        # Automatically support ETags and add the Content-Length header if
        # we have not flushed any content yet.
        if not self._headers_written:
            if (
                self._status_code == 200
                and self.request.method in ("GET", "HEAD")
                and "Etag" not in self._headers
            ):
                self.set_etag_header()
                if self.check_etag_header():
                    self._write_buffer = []
                    self.set_status(304)
            if self._status_code in (204, 304) or (100 <= self._status_code < 200):
                assert not self._write_buffer, (
                    "Cannot send body with %s" % self._status_code
                )
                self._clear_representation_headers()
            elif "Content-Length" not in self._headers:
                content_length = sum(len(part) for part in self._write_buffer)
                self.set_header("Content-Length", content_length)

        assert self.request.connection is not None
        # Now that the request is finished, clear the callback we
        # set on the HTTPConnection (which would otherwise prevent the
        # garbage collection of the RequestHandler when there
        # are keepalive connections)
        self.request.connection.set_close_callback(None)  # type: ignore

        future = self.flush(include_footers=True)
        self.request.connection.finish()
        self._log()
        self._finished = True
        self.on_finish()
        self._break_cycles()
        return future

    def detach(self) -> iostream.IOStream:
        """Take control of the underlying stream.
        控制底层流

        Returns the underlying `.IOStream` object and stops all
        further HTTP processing. Intended for implementing protocols
        like websockets that tunnel over an HTTP handshake.
        返回`IOStream`对象并且停止所有进一步HTTP处理。用于实现通过
        HTTP握手进行隧道传输的WebSocket之类的协议

        This method is only supported when HTTP/1.1 is used.

        .. versionadded:: 5.1
        """
        self._finished = True
        # TODO: add detach to HTTPConnection?
        return self.request.connection.detach()  # type: ignore

    def _break_cycles(self) -> None:
        # Break up a reference cycle between this handler and the
        # _ui_module closures to allow for faster GC on CPython.
        self.ui = None  # type: ignore

    def send_error(self, status_code: int = 500, **kwargs: Any) -> None:
        """Sends the given HTTP error code to the browser.
        向浏览器发送给定的HTTP错误码

        If `flush()` has already been called, it is not possible to send
        an error, so this method will simply terminate the response.
        If output has been written but not yet flushed, it will be discarded
        and replaced with the error page.
        如果`flush()`已被调用，此方法错误不会发出，所以这个方法将终止响应。
        如果输出只是写入没有flush,输出内容将被丢弃并被错误页替代

        Override `write_error()` to customize the error page that is returned.
        Additional keyword arguments are passed through to `write_error`.
        重写`write_error()`自定义返回错误页面。
        其他参数将传递给`write_error()`
        """
        if self._headers_written:
            gen_log.error("Cannot send error response after headers written")
            if not self._finished:
                # If we get an error between writing headers and finishing,
                # we are unlikely to be able to finish due to a
                # Content-Length mismatch. Try anyway to release the
                # socket.
                try:
                    self.finish()
                except Exception:
                    gen_log.error("Failed to flush partial response", exc_info=True)
            return
        self.clear()

        reason = kwargs.get("reason")
        if "exc_info" in kwargs:
            exception = kwargs["exc_info"][1]
            if isinstance(exception, HTTPError) and exception.reason:
                reason = exception.reason
        self.set_status(status_code, reason=reason)
        try:
            self.write_error(status_code, **kwargs)
        except Exception:
            app_log.error("Uncaught exception in write_error", exc_info=True)
        if not self._finished:
            self.finish()

    def write_error(self, status_code: int, **kwargs: Any) -> None:
        """Override to implement custom error pages.
        重写实现自定义错误页面

        ``write_error`` may call `write`, `render`, `set_header`, etc
        to produce output as usual.
        `write_error`可能会调用`write`,`render`,`set_header`等来产生一般输出。

        If this error was caused by an uncaught exception (including
        HTTPError), an ``exc_info`` triple will be available as
        ``kwargs["exc_info"]``.  Note that this exception may not be
        the "current" exception for purposes of methods like
        ``sys.exc_info()`` or ``traceback.format_exc``.
        如果这个错误是由未捕获的异常造成（包含HTTPError）,并且`exc_info`关键字
        在kwargs中。注意，对于`sys.exc_info()`或`traceback.format_exc`，
        此异常可能不是`当前`异常
        """
        if self.settings.get("serve_traceback") and "exc_info" in kwargs:
            # in debug mode, try to send a traceback
            self.set_header("Content-Type", "text/plain")
            for line in traceback.format_exception(*kwargs["exc_info"]):
                self.write(line)
            self.finish()
        else:
            self.finish(
                "<html><title>%(code)d: %(message)s</title>"
                "<body>%(code)d: %(message)s</body></html>"
                % {"code": status_code, "message": self._reason}
            )

    @property
    def locale(self) -> tornado.locale.Locale:
        """The locale for the current session.
        返回当前session的位置

        Determined by either `get_user_locale`, which you can override to
        set the locale based on, e.g., a user preference stored in a
        database, or `get_browser_locale`, which uses the ``Accept-Language``
        header.
        通过`get_user_locale`方法确定，且可以通过重写来设置locale的条件。
        用户偏好记录在数据库中或通过`get_browser_locale`方法获得`Accept-Language`头

        .. versionchanged: 4.1
           Added a property setter.
        """
        if not hasattr(self, "_locale"):
            loc = self.get_user_locale()
            if loc is not None:
                self._locale = loc
            else:
                self._locale = self.get_browser_locale()
                assert self._locale
        return self._locale

    @locale.setter
    def locale(self, value: tornado.locale.Locale) -> None:
        self._locale = value

    def get_user_locale(self) -> Optional[tornado.locale.Locale]:
        """Override to determine the locale from the authenticated user.
        重写此方法确定认证过的用户所在位置

        If None is returned, we fall back to `get_browser_locale()`.
        如果返回None，将会调用`get_browser_locale()`

        This method should return a `tornado.locale.Locale` object,
        most likely obtained via a call like ``tornado.locale.get("en")``
        此方法应返回`tornado.local.Locale`对象，
        就像调用`tornado.locale.get("en")`获得的一样
        """
        return None

    def get_browser_locale(self, default: str = "en_US") -> tornado.locale.Locale:
        """Determines the user's locale from ``Accept-Language`` header.
        从`Accept-Language`决定用户的位置。

        See http://www.w3.org/Protocols/rfc2616/rfc2616-sec14.html#sec14.4
        """
        if "Accept-Language" in self.request.headers:
            languages = self.request.headers["Accept-Language"].split(",")
            locales = []
            for language in languages:
                parts = language.strip().split(";")
                if len(parts) > 1 and parts[1].startswith("q="):
                    try:
                        score = float(parts[1][2:])
                    except (ValueError, TypeError):
                        score = 0.0
                else:
                    score = 1.0
                locales.append((parts[0], score))
            if locales:
                locales.sort(key=lambda pair: pair[1], reverse=True)
                codes = [loc[0] for loc in locales]
                return locale.get(*codes)
        return locale.get(default)

    @property
    def current_user(self) -> Any:
        """The authenticated user for this request.
        获得请求中被认证的用户。

        This is set in one of two ways:
        可使用以下两种方法中的一种来设置：

        * A subclass may override `get_current_user()`, which will be called
          automatically the first time ``self.current_user`` is accessed.
          `get_current_user()` will only be called once per request,
          and is cached for future access::
          子类可重写`get_current_user()`,`self.current_user`将自动在第一次访问调用，
          `get_current_user()`会在每次请求时调用一次，并且为新的访问做缓存

              def get_current_user(self):
                  user_cookie = self.get_secure_cookie("user")
                  if user_cookie:
                      return json.loads(user_cookie)
                  return None

        * It may be set as a normal variable, typically from an overridden
          `prepare()`::
          也可被设置为一个普通变量，通常通过重写prepare()实现

              @gen.coroutine
              def prepare(self):
                  user_id_cookie = self.get_secure_cookie("user_id")
                  if user_id_cookie:
                      self.current_user = yield load_user(user_id_cookie)

        Note that `prepare()` may be a coroutine while `get_current_user()`
        may not, so the latter form is necessary if loading the user requires
        asynchronous operations.
        注意`prepare()`可能是一个协程，但`get_current_user()`可能不是，所以加载用户需要
        使用异步的形式

        The user object may be any type of the application's choosing.
        用户对象可以是application选择的任意类型。
        """
        if not hasattr(self, "_current_user"):
            self._current_user = self.get_current_user()
        return self._current_user

    @current_user.setter
    def current_user(self, value: Any) -> None:
        self._current_user = value

    def get_current_user(self) -> Any:
        """Override to determine the current user from, e.g., a cookie.
        重写此方法来实现获取当前用户

        This method may not be a coroutine.
        这个方法可能不是一个协程
        """
        return None

    def get_login_url(self) -> str:
        """Override to customize the login URL based on the request.
        重写此方法可自定义请求的登录URL
        By default, we use the ``login_url`` application setting.
        默认情况下，我们使用application设置中的login_url
        """
        self.require_setting("login_url", "@tornado.web.authenticated")
        return self.application.settings["login_url"]

    def get_template_path(self) -> Optional[str]:
        """Override to customize template path for each handler.
        重写此方法可自定义每个handler的模板路径

        By default, we use the ``template_path`` application setting.
        Return None to load templates relative to the calling file.
        默认情况下，使用application设置中的`template_path`,如果返回空则使用
        调用文件的相对路径加载模板。
        """
        return self.application.settings.get("template_path")

    @property
    def xsrf_token(self) -> bytes:
        """The XSRF-prevention token for the current user/session.
        当前用户/会话的XSRF-prevention token

        To prevent cross-site request forgery, we set an '_xsrf' cookie
        and include the same '_xsrf' value as an argument with all POST
        requests. If the two do not match, we reject the form submission
        as a potential forgery.
        为了防止伪造跨站请求，设置一个'_xsrf' cookie 并在所有POST请求中包含相同的
        `_xsrf`值作为一个参数，如果这两个不匹配，我们会把这个提交当作潜在的伪造请求而
        拒绝请求

        See http://en.wikipedia.org/wiki/Cross-site_request_forgery

        This property is of type `bytes`, but it contains only ASCII
        characters. If a character string is required, there is no
        need to base64-encode it; just decode the byte string as
        UTF-8.
        这个属性的类型是`bytes`,但是只包含ASCII码字符。如果需要string，不用
        `base64-encode`,直接decode,编码使用UTF-8

        .. versionchanged:: 3.2.2
           The xsrf token will now be have a random mask applied in every
           request, which makes it safe to include the token in pages
           that are compressed.  See http://breachattack.com for more
           information on the issue fixed by this change.  Old (version 1)
           cookies will be converted to version 2 when this method is called
           unless the ``xsrf_cookie_version`` `Application` setting is
           set to 1.
           现在xsrf token 已经在每个请求都有一个随机mask，这样页面中包含token是完全的。
           查看 `http://breachattack.com`获得更多信息。这个方法被调用会把旧版token
           版本1变为版本2，除非`xsrf_cookie_version`在application中设置为1

        .. versionchanged:: 4.3
           The ``xsrf_cookie_kwargs`` `Application` setting may be
           used to supply additional cookie options (which will be
           passed directly to `set_cookie`). For example,
           ``xsrf_cookie_kwargs=dict(httponly=True, secure=True)``
           will set the ``secure`` and ``httponly`` flags on the
           ``_xsrf`` cookie.
           `xsrf_cookie_kwargs`在Application设置中，可以支持cokie的其他选项
           （会直接传递给`set_cookie`）,例如：
            ``xsrf_cookie_kwargs=dict(httponly=True, secure=True)``
           会把``secure`` 和 ``httponly`` 设置到``_xsrf`` cookie.
        """
        if not hasattr(self, "_xsrf_token"):
            version, token, timestamp = self._get_raw_xsrf_token()
            output_version = self.settings.get("xsrf_cookie_version", 2)
            cookie_kwargs = self.settings.get("xsrf_cookie_kwargs", {})
            if output_version == 1:
                self._xsrf_token = binascii.b2a_hex(token)
            elif output_version == 2:
                mask = os.urandom(4)
                self._xsrf_token = b"|".join(
                    [
                        b"2",
                        binascii.b2a_hex(mask),
                        binascii.b2a_hex(_websocket_mask(mask, token)),
                        utf8(str(int(timestamp))),
                    ]
                )
            else:
                raise ValueError("unknown xsrf cookie version %d", output_version)
            if version is None:
                if self.current_user and "expires_days" not in cookie_kwargs:
                    cookie_kwargs["expires_days"] = 30
                self.set_cookie("_xsrf", self._xsrf_token, **cookie_kwargs)
        return self._xsrf_token

    def _get_raw_xsrf_token(self) -> Tuple[Optional[int], bytes, float]:
        """Read or generate the xsrf token in its raw form.
        读取或生成原来格式的xsrf token

        The raw_xsrf_token is a tuple containing:
        raw_xsrf_token是一个元组，包含：

        * version: the version of the cookie from which this token was read,
          or None if we generated a new token in this request.
          从token中读取cookie版本，或者生成token得到None

        * token: the raw token data; random (non-ascii) bytes.
        原始的token或者随机的bytes
        * timestamp: the time this token was generated (will not be accurate
          for version 1 cookies)
          token生成的时间（1版本的cookie不一定准确）
        """
        if not hasattr(self, "_raw_xsrf_token"):
            cookie = self.get_cookie("_xsrf")
            if cookie:
                version, token, timestamp = self._decode_xsrf_token(cookie)
            else:
                version, token, timestamp = None, None, None
            if token is None:
                version = None
                token = os.urandom(16)
                timestamp = time.time()
            assert token is not None
            assert timestamp is not None
            self._raw_xsrf_token = (version, token, timestamp)
        return self._raw_xsrf_token

    def _decode_xsrf_token(
        self, cookie: str
    ) -> Tuple[Optional[int], Optional[bytes], Optional[float]]:
        """Convert a cookie string into a the tuple form returned by
        _get_raw_xsrf_token.
        把_get_raw_xsrf_token生成的cookie字符串转化为元组
        """

        try:
            m = _signed_value_version_re.match(utf8(cookie))

            if m:
                version = int(m.group(1))
                if version == 2:
                    _, mask_str, masked_token, timestamp_str = cookie.split("|")

                    mask = binascii.a2b_hex(utf8(mask_str))
                    token = _websocket_mask(mask, binascii.a2b_hex(utf8(masked_token)))
                    timestamp = int(timestamp_str)
                    return version, token, timestamp
                else:
                    # Treat unknown versions as not present instead of failing.
                    raise Exception("Unknown xsrf cookie version")
            else:
                version = 1
                try:
                    token = binascii.a2b_hex(utf8(cookie))
                except (binascii.Error, TypeError):
                    token = utf8(cookie)
                # We don't have a usable timestamp in older versions.
                timestamp = int(time.time())
                return (version, token, timestamp)
        except Exception:
            # Catch exceptions and return nothing instead of failing.
            gen_log.debug("Uncaught exception in _decode_xsrf_token", exc_info=True)
            return None, None, None

    def check_xsrf_cookie(self) -> None:
        """Verifies that the ``_xsrf`` cookie matches the ``_xsrf`` argument.
        确认`_xsrf` cookie与参数`_xsrf`匹配

        To prevent cross-site request forgery, we set an ``_xsrf``
        cookie and include the same value as a non-cookie
        field with all ``POST`` requests. If the two do not match, we
        reject the form submission as a potential forgery.
        为了防止跨站伪造请求，设置一个`_xsrf`cookie和包含同样值的non-cookie字段
        在每个post请求中。如果这两个都不匹配，将直接拒绝请求

        The ``_xsrf`` value may be set as either a form field named ``_xsrf``
        or in a custom HTTP header named ``X-XSRFToken`` or ``X-CSRFToken``
        (the latter is accepted for compatibility with Django).
        `_xsrf`值可设置在表单中，名称为`_xsrf`或在自定义的请求头中，名称是
        ``X-XSRFToken``/``X-CSRFToken``（）

        See http://en.wikipedia.org/wiki/Cross-site_request_forgery

        .. versionchanged:: 3.2.2
           Added support for cookie version 2.  Both versions 1 and 2 are
           supported.
           添加对版本2的支持，现在1和2两个版本都支持
        """
        # Prior to release 1.1.1, this check was ignored if the HTTP header
        # ``X-Requested-With: XMLHTTPRequest`` was present.  This exception
        # has been shown to be insecure and has been removed.  For more
        # information please see
        # http://www.djangoproject.com/weblog/2011/feb/08/security/
        # http://weblog.rubyonrails.org/2011/2/8/csrf-protection-bypass-in-ruby-on-rails
        token = (
            self.get_argument("_xsrf", None)
            or self.request.headers.get("X-Xsrftoken")
            or self.request.headers.get("X-Csrftoken")
        )
        if not token:
            raise HTTPError(403, "'_xsrf' argument missing from POST")
        _, token, _ = self._decode_xsrf_token(token)
        _, expected_token, _ = self._get_raw_xsrf_token()
        if not token:
            raise HTTPError(403, "'_xsrf' argument has invalid format")
        if not hmac.compare_digest(utf8(token), utf8(expected_token)):
            raise HTTPError(403, "XSRF cookie does not match POST argument")

    def xsrf_form_html(self) -> str:
        """An HTML ``<input/>`` element to be included with all POST forms.
        所有请求都将包含HTML`<input/>`标签

        It defines the ``_xsrf`` input value, which we check on all POST
        requests to prevent cross-site request forgery. If you have set
        the ``xsrf_cookies`` application setting, you must include this
        HTML within all of your HTML forms.
        此标签定义了post请求中为检查伪造跨站请求的`_xsrf`的输入值。如果在application 设置中
        设置了`xsrf_cookies`,就必须在所有HTML表单中包含这个标签。

        In a template, this method should be called with ``{% module
        xsrf_form_html() %}``
        在模板里，这个方法应该使用这种方式`{% module xsrf_form_html() %}`调用

        See `check_xsrf_cookie()` above for more information.
        查看上面的`check-xsrf_cookie()`方法获得更多信息。
        """
        return (
            '<input type="hidden" name="_xsrf" value="'
            + escape.xhtml_escape(self.xsrf_token)
            + '"/>'
        )

    def static_url(
        self, path: str, include_host: Optional[bool] = None, **kwargs: Any
    ) -> str:
        """Returns a static URL for the given relative static file path.
        根据给定的静态文件相对路径，返回一个静态URL

        This method requires you set the ``static_path`` setting in your
        application (which specifies the root directory of your static
        files).
        这个方法需要在application设置中设置`static_path`(静态文件的根目录)

        This method returns a versioned url (by default appending
        ``?v=<signature>``), which allows the static files to be
        cached indefinitely.  This can be disabled by passing
        ``include_version=False`` (in the default implementation;
        other static file implementations are not required to support
        this, but they may support other options).
        此方法默认会返回一个带版本的URL（添加在url后面`?v=<signature>`）,这
        允许文件被一直缓存。关闭版本的方法传递`include_version=False`

        By default this method returns URLs relative to the current
        host, but if ``include_host`` is true the URL returned will be
        absolute.  If this handler has an ``include_host`` attribute,
        that value will be used as the default for all `static_url`
        calls that do not pass ``include_host`` as a keyword argument.
        默认情况此方法返回当前host的相对路径，如果`include_host`为真，url会返回
        绝对路径，如果handler有`include_host`属性，该值会自动被所有调用`static_url`使用，
        而无须将`include_host`作为参数传递。

        """
        self.require_setting("static_path", "static_url")
        get_url = self.settings.get(
            "static_handler_class", StaticFileHandler
        ).make_static_url

        if include_host is None:
            include_host = getattr(self, "include_host", False)

        if include_host:
            base = self.request.protocol + "://" + self.request.host
        else:
            base = ""

        return base + get_url(self.settings, path, **kwargs)

    def require_setting(self, name: str, feature: str = "this feature") -> None:
        """Raises an exception if the given app setting is not defined.
        如果给定的名称在application的设置中找不到，就抛出一个异常
        """

        if not self.application.settings.get(name):
            raise Exception(
                "You must define the '%s' setting in your "
                "application to use %s" % (name, feature)
            )

    def reverse_url(self, name: str, *args: Any) -> str:
        """Alias for `Application.reverse_url`.
        `Application.reverse_url`的别名方法
        """
        return self.application.reverse_url(name, *args)

    def compute_etag(self) -> Optional[str]:
        """Computes the etag header to be used for this request.
        计算此请求的头etag

        By default uses a hash of the content written so far.
        默认使用输出内容的hash值

        May be overridden to provide custom etag implementations,
        or may return None to disable tornado's default etag support.
        可以重写此方法自定义etag实现或者放回None来禁用tornado默认对etag的支持
        """
        hasher = hashlib.sha1()
        for part in self._write_buffer:
            hasher.update(part)
        return '"%s"' % hasher.hexdigest()

    def set_etag_header(self) -> None:
        """Sets the response's Etag header using ``self.compute_etag()``.
        设置Etag返回头，使用`self.compute_etag()`值

        Note: no header will be set if ``compute_etag()`` returns ``None``.
        注意：如果`compute_etag()`返回空将不会设置Etag

        This method is called automatically when the request is finished.
        这个方法自动在请求结束后调用
        """
        etag = self.compute_etag()
        if etag is not None:
            self.set_header("Etag", etag)

    def check_etag_header(self) -> bool:
        """Checks the ``Etag`` header against requests's ``If-None-Match``.
        针对请求的`If-None-Match`检查`Etag`` 头

        Returns ``True`` if the request's Etag matches and a 304 should be
        returned. For example::
        如果请求的Etag匹配将返回True，应该把http状态设置为304返回

            self.set_etag_header()
            if self.check_etag_header():
                self.set_status(304)
                return

        This method is called automatically when the request is finished,
        but may be called earlier for applications that override
        `compute_etag` and want to do an early check for ``If-None-Match``
        before completing the request.  The ``Etag`` header should be set
        (perhaps with `set_etag_header`) before calling this method.
        这个方法会在请求结束后自动调用，重写`compute_etag`后可提前在请求完成前调用此方法取检查
        `If-None-Match`。`Etag`请求头应在调用此方法前设置（方法set_etag_header）
        """
        computed_etag = utf8(self._headers.get("Etag", ""))
        # Find all weak and strong etag values from If-None-Match header
        # because RFC 7232 allows multiple etag values in a single header.
        etags = re.findall(
            br'\*|(?:W/)?"[^"]*"', utf8(self.request.headers.get("If-None-Match", ""))
        )
        if not computed_etag or not etags:
            return False

        match = False
        if etags[0] == b"*":
            match = True
        else:
            # Use a weak comparison when comparing entity-tags.
            def val(x: bytes) -> bytes:
                return x[2:] if x.startswith(b"W/") else x

            for etag in etags:
                if val(etag) == val(computed_etag):
                    match = True
                    break
        return match

    async def _execute(
        self, transforms: List["OutputTransform"], *args: bytes, **kwargs: bytes
    ) -> None:
        """Executes this request with the given output transforms.
        使用给定的输出transforms执行请求
        """
        self._transforms = transforms
        try:
            if self.request.method not in self.SUPPORTED_METHODS:
                raise HTTPError(405)
            self.path_args = [self.decode_argument(arg) for arg in args]
            self.path_kwargs = dict(
                (k, self.decode_argument(v, name=k)) for (k, v) in kwargs.items()
            )
            # If XSRF cookies are turned on, reject form submissions without
            # the proper cookie
            if self.request.method not in (
                "GET",
                "HEAD",
                "OPTIONS",
            ) and self.application.settings.get("xsrf_cookies"):
                self.check_xsrf_cookie()

            result = self.prepare()
            if result is not None:
                result = await result
            if self._prepared_future is not None:
                # Tell the Application we've finished with prepare()
                # and are ready for the body to arrive.
                future_set_result_unless_cancelled(self._prepared_future, None)
            if self._finished:
                return

            if _has_stream_request_body(self.__class__):
                # In streaming mode request.body is a Future that signals
                # the body has been completely received.  The Future has no
                # result; the data has been passed to self.data_received
                # instead.
                try:
                    await self.request._body_future
                except iostream.StreamClosedError:
                    return

            method = getattr(self, self.request.method.lower())
            result = method(*self.path_args, **self.path_kwargs)
            if result is not None:
                result = await result
            if self._auto_finish and not self._finished:
                self.finish()
        except Exception as e:
            try:
                self._handle_request_exception(e)
            except Exception:
                app_log.error("Exception in exception handler", exc_info=True)
            finally:
                # Unset result to avoid circular references
                result = None
            if self._prepared_future is not None and not self._prepared_future.done():
                # In case we failed before setting _prepared_future, do it
                # now (to unblock the HTTP server).  Note that this is not
                # in a finally block to avoid GC issues prior to Python 3.4.
                self._prepared_future.set_result(None)

    def data_received(self, chunk: bytes) -> Optional[Awaitable[None]]:
        """Implement this method to handle streamed request data.
        实现此方法来处理请求流数据

        Requires the `.stream_request_body` decorator.
        需要`.stream_request_body`装饰器

        May be a coroutine for flow control.
        可以是一个协程控制流
        """
        raise NotImplementedError()

    def _log(self) -> None:
        """Logs the current request.
        当前请求写日志

        Sort of deprecated since this functionality was moved to the
        Application, but left in place for the benefit of existing apps
        that have overridden this method.
        这个方法已过时，已移植到Application里。但是留在这里是为兼容重写此方法的应用
        """
        self.application.log_request(self)

    def _request_summary(self) -> str:
        return "%s %s (%s)" % (
            self.request.method,
            self.request.uri,
            self.request.remote_ip,
        )

    def _handle_request_exception(self, e: BaseException) -> None:
        if isinstance(e, Finish):
            # Not an error; just finish the request without logging.
            if not self._finished:
                self.finish(*e.args)
            return
        try:
            self.log_exception(*sys.exc_info())
        except Exception:
            # An error here should still get a best-effort send_error()
            # to avoid leaking the connection.
            app_log.error("Error in exception logger", exc_info=True)
        if self._finished:
            # Extra errors after the request has been finished should
            # be logged, but there is no reason to continue to try and
            # send a response.
            return
        if isinstance(e, HTTPError):
            self.send_error(e.status_code, exc_info=sys.exc_info())
        else:
            self.send_error(500, exc_info=sys.exc_info())

    def log_exception(
        self,
        typ: "Optional[Type[BaseException]]",
        value: Optional[BaseException],
        tb: Optional[TracebackType],
    ) -> None:
        """Override to customize logging of uncaught exceptions.
        重写此方法来自定义未捕获异常日志。

        By default logs instances of `HTTPError` as warnings without
        stack traces (on the ``tornado.general`` logger), and all
        other exceptions as errors with stack traces (on the
        ``tornado.application`` logger).
        默认HTTPError的日志实例作为警告（warning）没有堆栈追踪（`tornado.general`日志）
        其他作为错误日志带有堆栈追踪（`tornado.application` 日志）
        .. versionadded:: 3.1
        """
        if isinstance(value, HTTPError):
            if value.log_message:
                format = "%d %s: " + value.log_message
                args = [value.status_code, self._request_summary()] + list(value.args)
                gen_log.warning(format, *args)
        else:
            app_log.error(
                "Uncaught exception %s\n%r",
                self._request_summary(),
                self.request,
                exc_info=(typ, value, tb),  # type: ignore
            )

    def _ui_module(self, name: str, module: Type["UIModule"]) -> Callable[..., str]:
        def render(*args, **kwargs) -> str:  # type: ignore
            if not hasattr(self, "_active_modules"):
                self._active_modules = {}  # type: Dict[str, UIModule]
            if name not in self._active_modules:
                self._active_modules[name] = module(self)
            rendered = self._active_modules[name].render(*args, **kwargs)
            return rendered

        return render

    def _ui_method(self, method: Callable[..., str]) -> Callable[..., str]:
        return lambda *args, **kwargs: method(self, *args, **kwargs)

    def _clear_representation_headers(self) -> None:
        # 304 responses should not contain representation metadata
        # headers (defined in
        # https://tools.ietf.org/html/rfc7231#section-3.1)
        # not explicitly allowed by
        # https://tools.ietf.org/html/rfc7232#section-4.1
        headers = ["Content-Encoding", "Content-Language", "Content-Type"]
        for h in headers:
            self.clear_header(h)


def stream_request_body(cls: Type[RequestHandler]) -> Type[RequestHandler]:
    """Apply to `RequestHandler` subclasses to enable streaming body support.
    应用在`RequestHandler`的子类使其支持流式body
    
    This decorator implies the following changes:
    此方法意味着下面的改变：

    * `.HTTPServerRequest.body` is undefined, and body arguments will not
      be included in `RequestHandler.get_argument`.
      `.HTTPServerRequest.body`未定义且body参数没有包含到`RequestHandler.get_argument`
    * `RequestHandler.prepare` is called when the request headers have been
      read instead of after the entire body has been read.
      `RequestHandler.prepare`被调用是在请求头读完而不是整个body读完时。
    * The subclass must define a method ``data_received(self, data):``, which
      will be called zero or more times as data is available.  Note that
      if the request has an empty body, ``data_received`` may not be called.
      子类必须定义一个方法`data_received(self, data):`，这个方法在数据可用会被调用0或多次。
      注意如果请求的body为空`data-received`可能不会被调用。
    * ``prepare`` and ``data_received`` may return Futures (such as via
      ``@gen.coroutine``, in which case the next method will not be called
      until those futures have completed.
      `prepare`和`data_received`可能返回一个Future,此future完成前下一个方法不会被调用。
    * The regular HTTP method (``post``, ``put``, etc) will be called after
      the entire body has been read.
      标准的HTTP方法（`post`, `put`等）将在整个body读取完毕后调用

    See the `file receiver demo <https://github.com/tornadoweb/tornado/tree/master/demos/file_upload/>`_
    for example usage.
    """  # noqa: E501
    if not issubclass(cls, RequestHandler):
        raise TypeError("expected subclass of RequestHandler, got %r", cls)
    cls._stream_request_body = True
    return cls


def _has_stream_request_body(cls: Type[RequestHandler]) -> bool:
    if not issubclass(cls, RequestHandler):
        raise TypeError("expected subclass of RequestHandler, got %r", cls)
    return cls._stream_request_body


def removeslash(
    method: Callable[..., Optional[Awaitable[None]]]
) -> Callable[..., Optional[Awaitable[None]]]:
    """Use this decorator to remove trailing slashes from the request path.
    使用这个装饰器删除请求路径尾部的斜杠

    For example, a request to ``/foo/`` would redirect to ``/foo`` with this
    decorator. Your request handler mapping should use a regular expression
    like ``r'/foo/*'`` in conjunction with using the decorator.
    例如，使用这个装饰器请求`/foo/`会被重定向到`/foo`。请求handler应映射正则表达式类似
    `r'/foo/*`和装饰器结合
    """

    @functools.wraps(method)
    def wrapper(  # type: ignore
        self: RequestHandler, *args, **kwargs
    ) -> Optional[Awaitable[None]]:
        if self.request.path.endswith("/"):
            if self.request.method in ("GET", "HEAD"):
                uri = self.request.path.rstrip("/")
                if uri:  # don't try to redirect '/' to ''
                    if self.request.query:
                        uri += "?" + self.request.query
                    self.redirect(uri, permanent=True)
                    return None
            else:
                raise HTTPError(404)
        return method(self, *args, **kwargs)

    return wrapper


def addslash(
    method: Callable[..., Optional[Awaitable[None]]]
) -> Callable[..., Optional[Awaitable[None]]]:
    """Use this decorator to add a missing trailing slash to the request path.
    使用这个装饰器给请求路径尾部添加斜杠
    For example, a request to ``/foo`` would redirect to ``/foo/`` with this
    decorator. Your request handler mapping should use a regular expression
    like ``r'/foo/?'`` in conjunction with using the decorator.
    例如，使用这个装饰器请求`/foo`会被重定向到`/foo/`。请求handler应映射正则表达式类似
    `r'/foo/?`和装饰器结合
    """

    @functools.wraps(method)
    def wrapper(  # type: ignore
        self: RequestHandler, *args, **kwargs
    ) -> Optional[Awaitable[None]]:
        if not self.request.path.endswith("/"):
            if self.request.method in ("GET", "HEAD"):
                uri = self.request.path + "/"
                if self.request.query:
                    uri += "?" + self.request.query
                self.redirect(uri, permanent=True)
                return None
            raise HTTPError(404)
        return method(self, *args, **kwargs)

    return wrapper


class _ApplicationRouter(ReversibleRuleRouter):
    """Routing implementation used internally by `Application`.
    `Application`使用的内部路由实现

    Provides a binding between `Application` and `RequestHandler`.
    提供一个`Application`和`RequestHandler`的绑定
    This implementation extends `~.routing.ReversibleRuleRouter` in a couple of ways:
    这个实现通过几种方式扩展了`~.routing.ReversibleRuleRouter`
        * it allows to use `RequestHandler` subclasses as `~.routing.Rule` target and
          这允许`RequestHandler`子类作为目标
        * it allows to use a list/tuple of rules as `~.routing.Rule` target.
          这允许使用list/tuple的规则作为`~.routing.Rule`目标
        ``process_rule`` implementation will substitute this list with an appropriate
        `_ApplicationRouter` instance.
        `process_rule`实现将会替换列表为`_ApplicationRouter` 实例
    """

    def __init__(
        self, application: "Application", rules: Optional[_RuleList] = None
    ) -> None:
        """ 初始化，并将handler交由父类处理

        Args:
            application: Application 实例
            rules: 实现requesthandler的子类
        """
        assert isinstance(application, Application)
        self.application = application
        super().__init__(rules)

    def process_rule(self, rule: Rule) -> Rule:
        """ handler、url、name、params会包装成Rule，包装时handler是数组和元组时需要此方法做递归迭代，全部封装为Rule

        Args:
            rule: handler相关数据封装后的实例

        Returns: 返回rule

        """
        rule = super().process_rule(rule)

        if isinstance(rule.target, (list, tuple)):
            rule.target = _ApplicationRouter(
                self.application, rule.target  # type: ignore
            )

        return rule

    def get_target_delegate(
        self, target: Any, request: httputil.HTTPServerRequest, **target_params: Any
    ) -> Optional[httputil.HTTPMessageDelegate]:
        """ 对请求url对应的回调handler进行封装

        Args:
            target: 实际处理request请求handler
            request: 请求
            **target_params: 实际处理request的handler参数

        Returns: 如果target是RequestHandler返回_HandlerDelegate实例，否则返回父类的get_target_delegate返回值

        """
        if isclass(target) and issubclass(target, RequestHandler):
            return self.application.get_handler_delegate(
                request, target, **target_params
            )

        return super().get_target_delegate(target, request, **target_params)


class Application(ReversibleRouter):
    r"""A collection of request handlers that make up a web application.
    一个请求handler集合组成了web应用

    Instances of this class are callable and can be passed directly to
    HTTPServer to serve the application::
    这个类的实例是可调用且能直接传递给HTTPServer为应用程序提供服务

        application = web.Application([
            (r"/", MainPageHandler),
        ])
        http_server = httpserver.HTTPServer(application)
        http_server.listen(8080)
        ioloop.IOLoop.current().start()

    The constructor for this class takes in a list of `~.routing.Rule`
    objects or tuples of values corresponding to the arguments of
    `~.routing.Rule` constructor: ``(matcher, target, [target_kwargs], [name])``,
    the values in square brackets being optional. The default matcher is
    `~.routing.PathMatches`, so ``(regexp, target)`` tuples can also be used
    instead of ``(PathMatches(regexp), target)``.
    这个类的构造器带有一个包含`~.routing.Rule`对象的列表或者一个元组里的值符合
    `~.routing.Rule`构造器的参数``(matcher, target, [target_kwargs], [name])``,
    方括号里的值可选。默认的matcher是`~.routing.PathMatches`,当然也可用``(regexp, target)``
    替换为``(PathMatches(regexp), target)``

    A common routing target is a `RequestHandler` subclass, but you can also
    use lists of rules as a target, which create a nested routing configuration::
    一个普通路由对象是`RequestHandler`的子类，但是也可用rule对象列表作为路由对象，下面创建了一个
    嵌套的路由配置

        application = web.Application([
            (HostMatches("example.com"), [
                (r"/", MainPageHandler),
                (r"/feed", FeedHandler),
            ]),
        ])

    In addition to this you can use nested `~.routing.Router` instances,
    `~.httputil.HTTPMessageDelegate` subclasses and callables as routing targets
    (see `~.routing` module docs for more information).
    除此之外还可以使用签到的`~.routing.Router`实例，
    `~.httputil.HTTPMessageDelegate`的子类和回调作为路由的对象
    （查看`~.routing`模块文档可获得更多信息）

    When we receive requests, we iterate over the list in order and
    instantiate an instance of the first request class whose regexp
    matches the request path. The request class can be specified as
    either a class object or a (fully-qualified) name.
    当收到请求，会遍历路由集合找到匹配请求路径的第一个请求类并实例化。
    请求类可指定为一个类对象或一个名称

    A dictionary may be passed as the third element (``target_kwargs``)
    of the tuple, which will be used as keyword arguments to the handler's
    constructor and `~RequestHandler.initialize` method. This pattern
    is used for the `StaticFileHandler` in this example (note that a
    `StaticFileHandler` can be installed automatically with the
    static_path setting described below)::
    一个字典(``target_kwargs``)做作为路由tuple的第三个元素,这个会作为参数用于
    handler的构造函数和`~RequestHandler.initialize`方法。
    在这个例子中这个配置用于`StaticFileHandler`（注意设置中有static_path
    会自动指定`StaticFileHandler`
    ）

        application = web.Application([
            (r"/static/(.*)", web.StaticFileHandler, {"path": "/var/www"}),
        ])

    We support virtual hosts with the `add_handlers` method, which takes in
    a host regular expression as the first argument::
    `add_handlers`方法支持虚拟host,这里将host正则表达式作为第一个参数::

        application.add_handlers(r"www\.myhost\.com", [
            (r"/article/([0-9]+)", ArticleHandler),
        ])

    If there's no match for the current request's host, then ``default_host``
    parameter value is matched against host regular expressions.
    如果当前没有匹配请求的host，`default_host`参数值再次匹配host正则表达式


    .. warning::

       Applications that do not use TLS may be vulnerable to :ref:`DNS
       rebinding <dnsrebinding>` attacks. This attack is especially
       relevant to applications that only listen on ``127.0.0.1`` or
       other private networks. Appropriate host patterns must be used
       (instead of the default of ``r'.*'``) to prevent this risk. The
       ``default_host`` argument must not be used in applications that
       may be vulnerable to DNS rebinding.
       Applications没有使用TLS可能很难抵挡DNS重绑攻击。这个攻击专门攻击只监听`127.0.0.1`
       或其它私有网络的应用

    You can serve static files by sending the ``static_path`` setting
    as a keyword argument. We will serve those files from the
    ``/static/`` URI (this is configurable with the
    ``static_url_prefix`` setting), and we will serve ``/favicon.ico``
    and ``/robots.txt`` from the same directory.  A custom subclass of
    `StaticFileHandler` can be specified with the
    ``static_handler_class`` setting.
    提供静态文件需要在设置中设置`static_path`，静态文件会使用以``/static/``开始的URI
    （这个静态文件路径头配置在`static_url_prefix`）,且会从相同的文件夹中
    提供``/favicon.ico``和``/robots.txt``。一个自定义子类`StaticFileHandler`可在设置
    参数`static_handler_class`上指定。


    .. versionchanged:: 4.5
       Integration with the new `tornado.routing` module.

    """

    def __init__(
        self,
        handlers: Optional[_RuleList] = None,
        default_host: Optional[str] = None,
        transforms: Optional[List[Type["OutputTransform"]]] = None,
        **settings: Any
    ) -> None:
        """ web application 初始化

        Args:
            handlers: requesthandler的子类和url组成的集合，实现客户端对某个url请求的数据响应
            default_host: 默认host，用于验证请求的host与默认host是否一致
            transforms: 响应的数据做处理，比如压缩等
            **settings: 其他设置参数
        """
        if transforms is None:
            self.transforms = []  # type: List[Type[OutputTransform]]
            if settings.get("compress_response") or settings.get("gzip"):
                self.transforms.append(GZipContentEncoding)
        else:
            self.transforms = transforms
        self.default_host = default_host
        self.settings = settings
        self.ui_modules = {
            "linkify": _linkify,
            "xsrf_form_html": _xsrf_form_html,
            "Template": TemplateModule,
        }
        self.ui_methods = {}  # type: Dict[str, Callable[..., str]]
        self._load_ui_modules(settings.get("ui_modules", {}))
        self._load_ui_methods(settings.get("ui_methods", {}))
        if self.settings.get("static_path"):
            path = self.settings["static_path"]
            handlers = list(handlers or [])
            # 静态文件访问的前缀
            static_url_prefix = settings.get("static_url_prefix", "/static/")
            static_handler_class = settings.get(
                "static_handler_class", StaticFileHandler
            )
            static_handler_args = settings.get("static_handler_args", {})
            static_handler_args["path"] = path
            for pattern in [
                re.escape(static_url_prefix) + r"(.*)",  # tornado会把‘(.*)’的内容，拿到static_path路径下去查找对应文件
                r"/(favicon\.ico)",
                r"/(robots\.txt)",
            ]:
                handlers.insert(0, (pattern, static_handler_class, static_handler_args))
        if self.settings.get("debug"):
            self.settings.setdefault("autoreload", True)
            self.settings.setdefault("compiled_template_cache", False)
            self.settings.setdefault("static_hash_cache", False)
            self.settings.setdefault("serve_traceback", True)
        # 将解析后的handler保存到rules数组里, 如果url有name，还会保存一份到named_rules数组
        self.wildcard_router = _ApplicationRouter(self, handlers)
        self.default_router = _ApplicationRouter(
            self, [Rule(AnyMatches(), self.wildcard_router)]
        )
        
        # Automatically reload modified modules
        if self.settings.get("autoreload"):
            from tornado import autoreload

            autoreload.start()

    def listen(self, port: int, address: str = "", **kwargs: Any) -> HTTPServer:
        """ 创建HTTP SERVER，绑定端口和地址，添加handler回调

        Args:
            port: 端口
            address: 地址
            **kwargs: 其他参数

        Returns: HTTP server

        """
        """Starts an HTTP server for this application on the given port.
        使用给定的端口为应用启动一个HTTP服务

        This is a convenience alias for creating an `.HTTPServer`
        object and calling its listen method.  Keyword arguments not
        supported by `HTTPServer.listen <.TCPServer.listen>` are passed to the
        `.HTTPServer` constructor.  For advanced uses
        (e.g. multi-process mode), do not use this method; create an
        `.HTTPServer` and call its
        `.TCPServer.bind`/`.TCPServer.start` methods directly.
         这是一个方便的别名，用于创建`.HTTPServer` 对象并调用其listen方法。
         关键参数不支持由`HTTPServer.listen <.TCPServer.listen>` 传递给`.HTTPServer`构造函数。
         更高级的多线程模式，不要使用此方法；直接创建 `.HTTPServer`并
         调用`.TCPServer.bind`/`.TCPServer.start`方法

        Note that after calling this method you still need to call
        ``IOLoop.current().start()`` to start the server.
        注意在调用完以上方法后依然需要调用``IOLoop.current().start()``启动服务

        Returns the `.HTTPServer` object.

        .. versionchanged:: 4.3
           Now returns the `.HTTPServer` object.
        """

        server = HTTPServer(self, **kwargs)
        server.listen(port, address)
        return server

    def add_handlers(self, host_pattern: str, host_handlers: _RuleList) -> None:
        """ 添加handler

        Args:
            host_pattern: host
            host_handlers: handler 列表

        Returns:

        """
        """Appends the given handlers to our handler list.
        添加给定的handler到handler列表

        Host patterns are processed sequentially in the order they were
        added. All matching patterns will be considered.
        Host patterns会按照添加顺序依次处理，所有的匹配patterns都会被匹配
        """
        host_matcher = HostMatches(host_pattern)
        rule = Rule(host_matcher, _ApplicationRouter(self, host_handlers))

        self.default_router.rules.insert(-1, rule)

        if self.default_host is not None:
            self.wildcard_router.add_rules(
                [(DefaultHostMatches(self, host_matcher.host_pattern), host_handlers)]
            )

    def add_transform(self, transform_class: Type["OutputTransform"]) -> None:
        """ 添加response转换的类

        Args:
            transform_class: 转换类

        Returns:

        """
        self.transforms.append(transform_class)

    def _load_ui_methods(self, methods: Any) -> None:
        """ 加载ui的方法，可在页面导入使用，增加复用性

        Args:
            methods: 方法或模块

        Returns:

        """
        if isinstance(methods, types.ModuleType):
            self._load_ui_methods(dict((n, getattr(methods, n)) for n in dir(methods)))
        elif isinstance(methods, list):
            for m in methods:
                self._load_ui_methods(m)
        else:
            for name, fn in methods.items():
                if (
                    not name.startswith("_")
                    and hasattr(fn, "__call__")
                    and name[0].lower() == name[0]
                ):
                    self.ui_methods[name] = fn

    def _load_ui_modules(self, modules: Any) -> None:
        """ 加载ui的使用的模块，可在页面导入使用，增加复用性

        Args:
            modules: 模块

        Returns:

        """
        if isinstance(modules, types.ModuleType):
            self._load_ui_modules(dict((n, getattr(modules, n)) for n in dir(modules)))
        elif isinstance(modules, list):
            for m in modules:
                self._load_ui_modules(m)
        else:
            assert isinstance(modules, dict)
            for name, cls in modules.items():
                try:
                    if issubclass(cls, UIModule):
                        self.ui_modules[name] = cls
                except TypeError:
                    pass

    def __call__(
        self, request: httputil.HTTPServerRequest
    ) -> Optional[Awaitable[None]]:
        """ 过时的实现获得客户端请求的回调

        Args:
            request: 请求

        Returns:

        """
        # Legacy HTTPServer interface
        dispatcher = self.find_handler(request)
        return dispatcher.execute()

    def find_handler(
        self, request: httputil.HTTPServerRequest, **kwargs: Any
    ) -> "_HandlerDelegate":
        """ 查找客户端请求对应的处理handler，并将本次请求的链接参数全部封装到_HandlerDelegate类里。
            没有找到对应的handler，取配置的默认handler，配置也没有，就默认返回错误的handler。

        Args:
            request: 请求
            **kwargs: 其他参数

        Returns:_HandlerDelegate类实例

        """
        route = self.default_router.find_handler(request)
        if route is not None:
            return cast("_HandlerDelegate", route)

        if self.settings.get("default_handler_class"):
            return self.get_handler_delegate(
                request,
                self.settings["default_handler_class"],
                self.settings.get("default_handler_args", {}),
            )

        return self.get_handler_delegate(request, ErrorHandler, {"status_code": 404})

    def get_handler_delegate(
        self,
        request: httputil.HTTPServerRequest,
        target_class: Type[RequestHandler],
        target_kwargs: Optional[Dict[str, Any]] = None,
        path_args: Optional[List[bytes]] = None,
        path_kwargs: Optional[Dict[str, bytes]] = None,
    ) -> "_HandlerDelegate":
        """ 封装handler的请求及配置

        Args:
            request: 请求
            target_class: handler 类
            target_kwargs: handler 参数
            path_args: 请求参数
            path_kwargs: 请求参数

        Returns: _HandlerDelegate

        """
        """Returns `~.httputil.HTTPMessageDelegate` that can serve a request
        for application and `RequestHandler` subclass.
        返回`~.httputil.HTTPMessageDelegate`，此实例可以服务于应用的请求和`RequestHandler`子类

        :arg httputil.HTTPServerRequest request: current HTTP request.
        当前HTTP请求
        :arg RequestHandler target_class: a `RequestHandler` class.
        一个RequestHandler类
        :arg dict target_kwargs: keyword arguments for ``target_class`` constructor.
        `target_class`参数的构造函数参数字典
        :arg list path_args: positional arguments for ``target_class`` HTTP method that
            will be executed while handling a request (``get``, ``post`` or any other).
            `target_class`的HTTP 方法（·get·,`post`）参数,以list列表形式传入
        :arg dict path_kwargs: keyword arguments for ``target_class`` HTTP method.
         `target_class`的HTTP 方法（·get·,`post`）参数,以字典形式传入
        """
        return _HandlerDelegate(
            self, request, target_class, target_kwargs, path_args, path_kwargs
        )

    def reverse_url(self, name: str, *args: Any) -> str:
        """ 通过name返回handler的URL，配置URL路径必须用URLSpec包装。

        Args:
            name: url路径配置时的名称
            *args: 此参数用于替换带有正则url，如url无正则无须传递参数

        Returns: name对应的URL

        """
        """Returns a URL path for handler named ``name``
        通过handler命名的`name`返回URL路径
        The handler must be added to the application as a named `URLSpec`.
        handler 必须作为`URLSpec`添加到应用程序。

        Args will be substituted for capturing groups in the `URLSpec` regex.
        arts将会替换捕获`URLSpec`正则中的组
        They will be converted to strings if necessary, encoded as utf8,
        and url-escaped.
        如果需要将会转换为urf8和url-escaped的字符串
        """
        reversed_url = self.default_router.reverse_url(name, *args)
        if reversed_url is not None:
            return reversed_url

        raise KeyError("%s not found in named urls" % name)

    def log_request(self, handler: RequestHandler) -> None:
        """ 打印请求完成的状态、url、耗时等信息。也可自定义打印，需要在settings里设置log_function

        Args:
            handler: 请求处理的handler

        Returns: None

        """
        """Writes a completed HTTP request to the logs.
        一个完成的HTTP请求写入日志

        By default writes to the python root logger.  To change
        this behavior either subclass Application and override this method,
        or pass a function in the application settings dictionary as
        ``log_function``.
        默认会写入python根目录的日志，改变行为需要在Application子类重写此方法或者
        应用设置字典中设置`log_function`
        """
        if "log_function" in self.settings:
            self.settings["log_function"](handler)
            return
        if handler.get_status() < 400:
            log_method = access_log.info
        elif handler.get_status() < 500:
            log_method = access_log.warning
        else:
            log_method = access_log.error
        request_time = 1000.0 * handler.request.request_time()
        log_method(
            "%d %s %.2fms",
            handler.get_status(),
            handler._request_summary(),
            request_time,
        )


class _HandlerDelegate(httputil.HTTPMessageDelegate):
    def __init__(
        self,
        application: Application,
        request: httputil.HTTPServerRequest,
        handler_class: Type[RequestHandler],
        handler_kwargs: Optional[Dict[str, Any]],
        path_args: Optional[List[bytes]],
        path_kwargs: Optional[Dict[str, bytes]],
    ) -> None:
        self.application = application
        self.connection = request.connection
        self.request = request
        self.handler_class = handler_class
        self.handler_kwargs = handler_kwargs or {}
        self.path_args = path_args or []
        self.path_kwargs = path_kwargs or {}
        self.chunks = []  # type: List[bytes]
        self.stream_request_body = _has_stream_request_body(self.handler_class)

    def headers_received(
        self,
        start_line: Union[httputil.RequestStartLine, httputil.ResponseStartLine],
        headers: httputil.HTTPHeaders,
    ) -> Optional[Awaitable[None]]:
        if self.stream_request_body:
            self.request._body_future = Future()
            return self.execute()
        return None

    def data_received(self, data: bytes) -> Optional[Awaitable[None]]:
        if self.stream_request_body:
            return self.handler.data_received(data)
        else:
            self.chunks.append(data)
            return None

    def finish(self) -> None:
        if self.stream_request_body:
            future_set_result_unless_cancelled(self.request._body_future, None)
        else:
            self.request.body = b"".join(self.chunks)
            self.request._parse_body()
            self.execute()

    def on_connection_close(self) -> None:
        if self.stream_request_body:
            self.handler.on_connection_close()
        else:
            self.chunks = None  # type: ignore

    def execute(self) -> Optional[Awaitable[None]]:
        # If template cache is disabled (usually in the debug mode),
        # re-compile templates and reload static files on every
        # request so you don't need to restart to see changes
        if not self.application.settings.get("compiled_template_cache", True):
            with RequestHandler._template_loader_lock:
                for loader in RequestHandler._template_loaders.values():
                    loader.reset()
        if not self.application.settings.get("static_hash_cache", True):
            StaticFileHandler.reset()

        self.handler = self.handler_class(
            self.application, self.request, **self.handler_kwargs
        )
        transforms = [t(self.request) for t in self.application.transforms]

        if self.stream_request_body:
            self.handler._prepared_future = Future()
        # Note that if an exception escapes handler._execute it will be
        # trapped in the Future it returns (which we are ignoring here,
        # leaving it to be logged when the Future is GC'd).
        # However, that shouldn't happen because _execute has a blanket
        # except handler, and we cannot easily access the IOLoop here to
        # call add_future (because of the requirement to remain compatible
        # with WSGI)
        fut = gen.convert_yielded(
            self.handler._execute(transforms, *self.path_args, **self.path_kwargs)
        )
        fut.add_done_callback(lambda f: f.result())
        # If we are streaming the request body, then execute() is finished
        # when the handler has prepared to receive the body.  If not,
        # it doesn't matter when execute() finishes (so we return None)
        return self.handler._prepared_future


class HTTPError(Exception):
    """An exception that will turn into an HTTP error response.
    将http变成错误响应的异常

    Raising an `HTTPError` is a convenient alternative to calling
    `RequestHandler.send_error` since it automatically ends the
    current function.
    抛出一个`HTTPError`是一个更方便选择比起调用`RequestHandler.send_error`
    因为它会自动结束当前方法

    To customize the response sent with an `HTTPError`, override
    `RequestHandler.write_error`.
    自定义`HTTPError`响应内容，重写`RequestHandler.write_error`.

    :arg int status_code: HTTP status code.  Must be listed in
        `httplib.responses <http.client.responses>` unless the ``reason``
        keyword argument is given.
        HTTP状态码必须列在 `httplib.responses <http.client.responses>` 之中除非给定了
        ``reason`` 关键字参数.
    :arg str log_message: Message to be written to the log for this error
        (will not be shown to the user unless the `Application` is in debug
        mode).  May contain ``%s``-style placeholders, which will be filled
        in with remaining positional parameters.
        这个错误的信息会写入日志（不会展示给用户，除非`Application`是debug模式）
        可能含有%s占位符，它将填补剩余的位置参数
    :arg str reason: Keyword-only argument.  The HTTP "reason" phrase
        to pass in the status line along with ``status_code``.  Normally
        determined automatically from ``status_code``, but can be used
        to use a non-standard numeric code.
        唯一关键字参数。HTTP "reason"和"reason"一起传入状态行, 通常从`status_code`
        自动确定但也可以使用一个非标准的数字代码
    """

    def __init__(
        self,
        status_code: int = 500,
        log_message: Optional[str] = None,
        *args: Any,
        **kwargs: Any
    ) -> None:
        self.status_code = status_code
        self.log_message = log_message
        self.args = args
        self.reason = kwargs.get("reason", None)
        if log_message and not args:
            self.log_message = log_message.replace("%", "%%")

    def __str__(self) -> str:
        message = "HTTP %d: %s" % (
            self.status_code,
            self.reason or httputil.responses.get(self.status_code, "Unknown"),
        )
        if self.log_message:
            return message + " (" + (self.log_message % self.args) + ")"
        else:
            return message


class Finish(Exception):
    """An exception that ends the request without producing an error response.
    一个不会产生错误响应的请求结束异常

    When `Finish` is raised in a `RequestHandler`, the request will
    end (calling `RequestHandler.finish` if it hasn't already been
    called), but the error-handling methods (including
    `RequestHandler.write_error`) will not be called.
    当`Finish`在一个`RequestHandler`里被抛出，请求将会结束（如果该方法没有被调用，就
    调用`RequestHandler.finish`），但是错误处理方法不会被调用（
    包含`RequestHandler.write_error`）

    If `Finish()` was created with no arguments, the pending response
    will be sent as-is. If `Finish()` was given an argument, that
    argument will be passed to `RequestHandler.finish()`.
    如果创建Finish()没有带任何参数，则会发送一个原样pending响应。如果`Finish()`
    给定了参数，这些参数会传给`RequestHandler.finish()`

    This can be a more convenient way to implement custom error pages
    than overriding ``write_error`` (especially in library code)::
    这是比重写`write_error`更加方便的方式实现自定义错误页

        if self.current_user is None:
            self.set_status(401)
            self.set_header('WWW-Authenticate', 'Basic realm="something"')
            raise Finish()

    .. versionchanged:: 4.3
       Arguments passed to ``Finish()`` will be passed on to
       `RequestHandler.finish`.
       传递给`Finish()`的参数将会传递给`RequestHandler.finish`
    """

    pass


class MissingArgumentError(HTTPError):
    """Exception raised by `RequestHandler.get_argument`.
    `RequestHandler.get_argument` 会抛出此异常

    This is a subclass of `HTTPError`, so if it is uncaught a 400 response
    code will be used instead of 500 (and a stack trace will not be logged).
    这是一个`HTTPError`的子类，那么如果是未捕获的400响应码将会替换500(且栈追踪不会写入日志)

    .. versionadded:: 3.1
    """

    def __init__(self, arg_name: str) -> None:
        super().__init__(400, "Missing argument %s" % arg_name)
        self.arg_name = arg_name


class ErrorHandler(RequestHandler):
    """Generates an error response with ``status_code`` for all requests.
    为所有请求生成一个带有`status_code`的错误响应
    """

    def initialize(self, status_code: int) -> None:
        self.set_status(status_code)

    def prepare(self) -> None:
        raise HTTPError(self._status_code)

    def check_xsrf_cookie(self) -> None:
        # POSTs to an ErrorHandler don't actually have side effects,
        # so we don't need to check the xsrf token.  This allows POSTs
        # to the wrong url to return a 404 instead of 403.
        pass


class RedirectHandler(RequestHandler):
    """Redirects the client to the given URL for all GET requests.
    为所有GET请求重定向到给定的URL

    You should provide the keyword argument ``url`` to the handler, e.g.::
    应该给handler提供关键参数`url`
        application = web.Application([
            (r"/oldpath", web.RedirectHandler, {"url": "/newpath"}),
        ])

    `RedirectHandler` supports regular expression substitutions. E.g., to
    swap the first and second parts of a path while preserving the remainder::
    `RedirectHandler`支持正则表达式，交换路径的第一和第二部分同时保留剩余部分


        application = web.Application([
            (r"/(.*?)/(.*?)/(.*)", web.RedirectHandler, {"url": "/{1}/{0}/{2}"}),
        ])

    The final URL is formatted with `str.format` and the substrings that match
    the capturing groups. In the above example, a request to "/a/b/c" would be
    formatted like::
    最终URL是通过`r.format`子字符串匹配目标组。上面的例子，一个请求/a/b/c会格式化下面的形式

        str.format("/{1}/{0}/{2}", "a", "b", "c")  # -> "/b/a/c"

    Use Python's :ref:`format string syntax <formatstrings>` to customize how
    values are substituted.
    使用python的字符串格式语法自定义如何替换值

    .. versionchanged:: 4.5
       Added support for substitutions into the destination URL.
       新增支持替换到目标URL

    .. versionchanged:: 5.0
       If any query arguments are present, they will be copied to the
       destination URL.
       如果存在任何查询参数，它将会拷贝到目标URL
    """

    def initialize(self, url: str, permanent: bool = True) -> None:
        self._url = url
        self._permanent = permanent

    def get(self, *args: Any, **kwargs: Any) -> None:
        to_url = self._url.format(*args, **kwargs)
        if self.request.query_arguments:
            # TODO: figure out typing for the next line.
            to_url = httputil.url_concat(
                to_url,
                list(httputil.qs_to_qsl(self.request.query_arguments)),  # type: ignore
            )
        self.redirect(to_url, permanent=self._permanent)


class StaticFileHandler(RequestHandler):
    """A simple handler that can serve static content from a directory.
    一个简单的静态文件内容服务handler

    A `StaticFileHandler` is configured automatically if you pass the
    ``static_path`` keyword argument to `Application`.  This handler
    can be customized with the ``static_url_prefix``, ``static_handler_class``,
    and ``static_handler_args`` settings.
    如果将`static_path`配置到`Application`，则会自动配置`StaticFileHandler`，
    这个handler可使用专属的`static_url_prefix``, ``static_handler_class``,
    和``static_handler_args`配置

    To map an additional path to this handler for a static data directory
    you would add a line to your application like::
    要为静态数据目录映射到handler的附加路径，应该应用程序里添加下面这行
        application = web.Application([
            (r"/content/(.*)", web.StaticFileHandler, {"path": "/var/www"}),
        ])

    The handler constructor requires a ``path`` argument, which specifies the
    local root directory of the content to be served.
    这个handler的构造方法需要一个path参数，该参数指定服务的内容本地根目录

    Note that a capture group in the regex is required to parse the value for
    the ``path`` argument to the get() method (different than the constructor
    argument above); see `URLSpec` for details.
    请注意，正则表达式中的捕获组需要解析get（）方法的``path``参数的值（与上面的构造函数参数不同）；
    有关详细信息，请参见“URLSpec”。

    To serve a file like ``index.html`` automatically when a directory is
    requested, set ``static_handler_args=dict(default_filename="index.html")``
    in your application settings, or add ``default_filename`` as an initializer
    argument for your ``StaticFileHandler``.
    在请求目录时自动提供类似于``index.html``的文件,在应用设置中设置
    `static_handler_args=dict(default_filename="index.html")`或者
    将``default_filename``作为`StaticFileHandler`的初始化参数

    To maximize the effectiveness of browser caching, this class supports
    versioned urls (by default using the argument ``?v=``).  If a version
    is given, we instruct the browser to cache this file indefinitely.
    `make_static_url` (also available as `RequestHandler.static_url`) can
    be used to construct a versioned url.
    最大限度提供浏览器缓存效果，此类支持把url带版本（默认使用参数`?v=`）。如果给出一个版本，
    将会指定浏览器无限期的缓存。`make_static_url`可以构建一个带版本的url(也可作为`RequestHandler.static_url`)

    This handler is intended primarily for use in development and light-duty
    file serving; for heavy traffic it will be more efficient to use
    a dedicated static file server (such as nginx or Apache).  We support
    the HTTP ``Accept-Ranges`` mechanism to return partial content (because
    some browsers require this functionality to be present to seek in
    HTML5 audio or video).
    此handler主要用于开发和轻型文件服务; 对于比较重的应用使用文件服务器效果更好（比如nginx或者apache）.
    支持http`Accept-Ranges`机制返回部分内容（因为某些浏览器需要此设计支持HTML5声音和视频分段）

    **Subclassing notes**
    子类注意

    This class is designed to be extensible by subclassing, but because
    of the way static urls are generated with class methods rather than
    instance methods, the inheritance patterns are somewhat unusual.
    Be sure to use the ``@classmethod`` decorator when overriding a
    class method.  Instance methods may use the attributes ``self.path``
    ``self.absolute_path``, and ``self.modified``.
    此类被设计为可继承，但是由于静态url是类方法生成而不是实例方法生成，继承模式不同平常，
    重写类方法一定要使用`@classmethod`装饰器。实例方法可使用属性`self.path``
    ``self.absolute_path``和 ``self.modified``.

    Subclasses should only override methods discussed in this section;
    overriding other methods is error-prone.  Overriding
    ``StaticFileHandler.get`` is particularly problematic due to the
    tight coupling with ``compute_etag`` and other methods.
    子类应该仅重写本节讨论的方法;重写其它方法容易出错。重写`StaticFileHandler.get`
    特别容易出问题，因其与`compute_etag`和其它方法紧耦合

    To change the way static urls are generated (e.g. to match the behavior
    of another server or CDN), override `make_static_url`, `parse_url_path`,
    `get_cache_time`, and/or `get_version`.
    修改静态路径生成方式（匹配其它服务器或CDN行为），重写`make_static_url`, `parse_url_path`,
    `get_cache_time`, `get_version`

    To replace all interaction with the filesystem (e.g. to serve
    static content from a database), override `get_content`,
    `get_content_size`, `get_modified_time`, `get_absolute_path`, and
    `validate_absolute_path`.
    替换与文件系统的交互（从数据库提供静态内容），重写`get_content`,
    `get_content_size`, `get_modified_time`, `get_absolute_path`和
    `validate_absolute_path`.

    .. versionchanged:: 3.1
       Many of the methods for subclasses were added in Tornado 3.1.
       很对为子类设计的方法在tornado3.1被添加。
    """

    CACHE_MAX_AGE = 86400 * 365 * 10  # 10 years

    _static_hashes = {}  # type: Dict[str, Optional[str]]
    _lock = threading.Lock()  # protects _static_hashes

    def initialize(self, path: str, default_filename: Optional[str] = None) -> None:
        print(path,default_filename)
        self.root = path
        self.default_filename = default_filename

    @classmethod
    def reset(cls) -> None:
        with cls._lock:
            cls._static_hashes = {}

    def head(self, path: str) -> Awaitable[None]:
        return self.get(path, include_body=False)

    async def get(self, path: str, include_body: bool = True) -> None:
        # Set up our path instance variables.
        print(path)
        self.path = self.parse_url_path(path)
        del path  # make sure we don't refer to path instead of self.path again
        absolute_path = self.get_absolute_path(self.root, self.path)
        self.absolute_path = self.validate_absolute_path(self.root, absolute_path)
        if self.absolute_path is None:
            return

        self.modified = self.get_modified_time()
        self.set_headers()

        if self.should_return_304():
            self.set_status(304)
            return

        request_range = None
        range_header = self.request.headers.get("Range")
        if range_header:
            # As per RFC 2616 14.16, if an invalid Range header is specified,
            # the request will be treated as if the header didn't exist.
            request_range = httputil._parse_request_range(range_header)

        size = self.get_content_size()
        if request_range:
            start, end = request_range
            if start is not None and start < 0:
                start += size
                if start < 0:
                    start = 0
            if (
                start is not None
                and (start >= size or (end is not None and start >= end))
            ) or end == 0:
                # As per RFC 2616 14.35.1, a range is not satisfiable only: if
                # the first requested byte is equal to or greater than the
                # content, or when a suffix with length 0 is specified.
                # https://tools.ietf.org/html/rfc7233#section-2.1
                # A byte-range-spec is invalid if the last-byte-pos value is present
                # and less than the first-byte-pos.
                self.set_status(416)  # Range Not Satisfiable
                self.set_header("Content-Type", "text/plain")
                self.set_header("Content-Range", "bytes */%s" % (size,))
                return
            if end is not None and end > size:
                # Clients sometimes blindly use a large range to limit their
                # download size; cap the endpoint at the actual file size.
                end = size
            # Note: only return HTTP 206 if less than the entire range has been
            # requested. Not only is this semantically correct, but Chrome
            # refuses to play audio if it gets an HTTP 206 in response to
            # ``Range: bytes=0-``.
            if size != (end or size) - (start or 0):
                self.set_status(206)  # Partial Content
                self.set_header(
                    "Content-Range", httputil._get_content_range(start, end, size)
                )
        else:
            start = end = None

        if start is not None and end is not None:
            content_length = end - start
        elif end is not None:
            content_length = end
        elif start is not None:
            content_length = size - start
        else:
            content_length = size
        self.set_header("Content-Length", content_length)

        if include_body:
            content = self.get_content(self.absolute_path, start, end)
            if isinstance(content, bytes):
                content = [content]
            for chunk in content:
                try:
                    self.write(chunk)
                    await self.flush()
                except iostream.StreamClosedError:
                    return
        else:
            assert self.request.method == "HEAD"

    def compute_etag(self) -> Optional[str]:
        """Sets the ``Etag`` header based on static url version.
        基于静态路径版本设置`Etag`头

        This allows efficient ``If-None-Match`` checks against cached
        versions, and sends the correct ``Etag`` for a partial response
        (i.e. the same ``Etag`` as the full file).
        这允许针对缓存版本进行高效的“If-None-Match”检查，为部分响应发送正确的`Etag`

        .. versionadded:: 3.1
        """
        assert self.absolute_path is not None
        version_hash = self._get_cached_version(self.absolute_path)
        if not version_hash:
            return None
        return '"%s"' % (version_hash,)

    def set_headers(self) -> None:
        """Sets the content and caching headers on the response.
           设置响应的内容和缓存头

        .. versionadded:: 3.1
        """
        self.set_header("Accept-Ranges", "bytes")
        self.set_etag_header()

        if self.modified is not None:
            self.set_header("Last-Modified", self.modified)

        content_type = self.get_content_type()
        if content_type:
            self.set_header("Content-Type", content_type)

        cache_time = self.get_cache_time(self.path, self.modified, content_type)
        if cache_time > 0:
            self.set_header(
                "Expires",
                datetime.datetime.utcnow() + datetime.timedelta(seconds=cache_time),
            )
            self.set_header("Cache-Control", "max-age=" + str(cache_time))

        self.set_extra_headers(self.path)

    def should_return_304(self) -> bool:
        """Returns True if the headers indicate that we should return 304.
        如果头部显示应返回304，则返回True

        .. versionadded:: 3.1
        """
        # If client sent If-None-Match, use it, ignore If-Modified-Since
        if self.request.headers.get("If-None-Match"):
            return self.check_etag_header()

        # Check the If-Modified-Since, and don't send the result if the
        # content has not been modified
        ims_value = self.request.headers.get("If-Modified-Since")
        if ims_value is not None:
            date_tuple = email.utils.parsedate(ims_value)
            if date_tuple is not None:
                if_since = datetime.datetime(*date_tuple[:6])
                assert self.modified is not None
                if if_since >= self.modified:
                    return True

        return False

    @classmethod
    def get_absolute_path(cls, root: str, path: str) -> str:
        """Returns the absolute location of ``path`` relative to ``root``.
        返回path相对于root的绝对路径

        ``root`` is the path configured for this `StaticFileHandler`
        (in most cases the ``static_path`` `Application` setting).
        root是`StaticFileHandler`配置的路径（在多数情况是`Application`设置的`static_path`）

        This class method may be overridden in subclasses.  By default
        it returns a filesystem path, but other strings may be used
        as long as they are unique and understood by the subclass's
        overridden `get_content`.
        此方法可在子类重写。默认放回文件系统路径，但是其它字符串也可使用，只要是唯一且能
        被子类重写的`get_content`使用。

        .. versionadded:: 3.1
        """
        abspath = os.path.abspath(os.path.join(root, path))
        return abspath

    def validate_absolute_path(self, root: str, absolute_path: str) -> Optional[str]:
        """Validate and return the absolute path.
        返回验证后的绝对路径

        ``root`` is the configured path for the `StaticFileHandler`,
        and ``path`` is the result of `get_absolute_path`
        `root`是为`StaticFileHandler`配置的路径，
        `path`是`get_absolute_path`返回的结果

        This is an instance method called during request processing,
        so it may raise `HTTPError` or use methods like
        `RequestHandler.redirect` (return None after redirecting to
        halt further processing).  This is where 404 errors for missing files
        are generated.
        这是一个实例方法在请求过程中被调用，所有它可能抛出`HTTPError`或者使用类似（
        在重定向到停止进一步处理之后返回None)这种方法。文件丢失会生成404错误。

        This method may modify the path before returning it, but note that
        any such modifications will not be understood by `make_static_url`.
        此方法可能在返回路径之前修改路径，但是需要注意任何修改`make_static_url`不会知道

        In instance methods, this method's result is available as
        ``self.absolute_path``.
        在实例方法中，此方法的结果`self.absolute_path`可用

        .. versionadded:: 3.1
        """
        # os.path.abspath strips a trailing /.
        # We must add it back to `root` so that we only match files
        # in a directory named `root` instead of files starting with
        # that prefix.
        root = os.path.abspath(root)
        if not root.endswith(os.path.sep):
            # abspath always removes a trailing slash, except when
            # root is '/'. This is an unusual case, but several projects
            # have independently discovered this technique to disable
            # Tornado's path validation and (hopefully) do their own,
            # so we need to support it.
            root += os.path.sep
        # The trailing slash also needs to be temporarily added back
        # the requested path so a request to root/ will match.
        if not (absolute_path + os.path.sep).startswith(root):
            raise HTTPError(403, "%s is not in root static directory", self.path)
        if os.path.isdir(absolute_path) and self.default_filename is not None:
            # need to look at the request.path here for when path is empty
            # but there is some prefix to the path that was already
            # trimmed by the routing
            if not self.request.path.endswith("/"):
                self.redirect(self.request.path + "/", permanent=True)
                return None
            absolute_path = os.path.join(absolute_path, self.default_filename)
        if not os.path.exists(absolute_path):
            raise HTTPError(404)
        if not os.path.isfile(absolute_path):
            raise HTTPError(403, "%s is not a file", self.path)
        return absolute_path

    @classmethod
    def get_content(
        cls, abspath: str, start: Optional[int] = None, end: Optional[int] = None
    ) -> Generator[bytes, None, None]:
        """Retrieve the content of the requested resource which is located
        at the given absolute path.
        检索给定的本地绝对路径上的请求资源内容

        This class method may be overridden by subclasses.  Note that its
        signature is different from other overridable class methods
        (no ``settings`` argument); this is deliberate to ensure that
        ``abspath`` is able to stand on its own as a cache key.
        此类方法可被子类重写，注意此类方法不同于其它可重写类方法（没有`settings`参数）；
        经过深思熟虑以确保`abspath`可依靠自身作为缓存键。

        This method should either return a byte string or an iterator
        of byte strings.  The latter is preferred for large files
        as it helps reduce memory fragmentation.
        次方应返回一个字节字符串或者一个字节字符串迭代器。对于大文件后者是最有选择
        ，它有助于减少内存碎片。

        .. versionadded:: 3.1
        """
        with open(abspath, "rb") as file:
            if start is not None:
                file.seek(start)
            if end is not None:
                remaining = end - (start or 0)  # type: Optional[int]
            else:
                remaining = None
            while True:
                chunk_size = 64 * 1024
                if remaining is not None and remaining < chunk_size:
                    chunk_size = remaining
                chunk = file.read(chunk_size)
                if chunk:
                    if remaining is not None:
                        remaining -= len(chunk)
                    yield chunk
                else:
                    if remaining is not None:
                        assert remaining == 0
                    return

    @classmethod
    def get_content_version(cls, abspath: str) -> str:
        """Returns a version string for the resource at the given path.
        返回给定路径的资源版本字符串

        This class method may be overridden by subclasses.  The
        default implementation is a SHA-512 hash of the file's contents.
        此类方法可被子类重写。默认实现一个文件内容SHA-512 hash

        .. versionadded:: 3.1
        """
        data = cls.get_content(abspath)
        hasher = hashlib.sha512()
        if isinstance(data, bytes):
            hasher.update(data)
        else:
            for chunk in data:
                hasher.update(chunk)
        return hasher.hexdigest()

    def _stat(self) -> os.stat_result:
        assert self.absolute_path is not None
        if not hasattr(self, "_stat_result"):
            self._stat_result = os.stat(self.absolute_path)
        return self._stat_result

    def get_content_size(self) -> int:
        """Retrieve the total size of the resource at the given path.
        检索给定路径资源的总大小。

        This method may be overridden by subclasses.
        此方法可被子类重写

        .. versionadded:: 3.1

        .. versionchanged:: 4.0
           This method is now always called, instead of only when
           partial results are requested.
           现在总是调用此方法，而不是在请求部分结果时才调用
        """
        stat_result = self._stat()
        return stat_result.st_size

    def get_modified_time(self) -> Optional[datetime.datetime]:
        """Returns the time that ``self.absolute_path`` was last modified.
        返回`self.absolute_path`最后修改时间

        May be overridden in subclasses.  Should return a `~datetime.datetime`
        object or None.
        可被子类重写，应放回一个`~datetime.datetime`对象或None

        .. versionadded:: 3.1
        """
        stat_result = self._stat()
        # NOTE: Historically, this used stat_result[stat.ST_MTIME],
        # which truncates the fractional portion of the timestamp. It
        # was changed from that form to stat_result.st_mtime to
        # satisfy mypy (which disallows the bracket operator), but the
        # latter form returns a float instead of an int. For
        # consistency with the past (and because we have a unit test
        # that relies on this), we truncate the float here, although
        # I'm not sure that's the right thing to do.
        modified = datetime.datetime.utcfromtimestamp(int(stat_result.st_mtime))
        return modified

    def get_content_type(self) -> str:
        """Returns the ``Content-Type`` header to be used for this request.
        返回请求使用`Content-Type`头

        .. versionadded:: 3.1
        """
        assert self.absolute_path is not None
        mime_type, encoding = mimetypes.guess_type(self.absolute_path)
        # per RFC 6713, use the appropriate type for a gzip compressed file
        if encoding == "gzip":
            return "application/gzip"
        # As of 2015-07-21 there is no bzip2 encoding defined at
        # http://www.iana.org/assignments/media-types/media-types.xhtml
        # So for that (and any other encoding), use octet-stream.
        elif encoding is not None:
            return "application/octet-stream"
        elif mime_type is not None:
            return mime_type
        # if mime_type not detected, use application/octet-stream
        else:
            return "application/octet-stream"

    def set_extra_headers(self, path: str) -> None:
        """For subclass to add extra headers to the response
        方便子类添加额外的返回头
        """
        pass

    def get_cache_time(
        self, path: str, modified: Optional[datetime.datetime], mime_type: str
    ) -> int:
        """Override to customize cache control behavior.
        重写来自定义缓存控制行为

        Return a positive number of seconds to make the result
        cacheable for that amount of time or 0 to mark resource as
        cacheable for an unspecified amount of time (subject to
        browser heuristics).
        返回正秒数以使结果在该时间段内可缓存，或返回0以将资源标记为在未指定的时间段内可缓存
        （受浏览器自身的影响）


        By default returns cache expiry of 10 years for resources requested
        with ``v`` argument.
        默认情况下带有 ``v`` 请求参数的资源返回的缓存过期时间是10年.
        """
        return self.CACHE_MAX_AGE if "v" in self.request.arguments else 0

    @classmethod
    def make_static_url(
        cls, settings: Dict[str, Any], path: str, include_version: bool = True
    ) -> str:
        """Constructs a versioned url for the given path.
        为给定的路径构建一个带版本的url

        This method may be overridden in subclasses (but note that it
        is a class method rather than an instance method).  Subclasses
        are only required to implement the signature
        ``make_static_url(cls, settings, path)``; other keyword
        arguments may be passed through `~RequestHandler.static_url`
        but are not standard.
        此方法可被子类重写（但是需要注意此方法是类方法而不是实例方法），子类仅需实现
        `make_static_url(cls, settings, path)`；其它参数通过
        `~RequestHandler.static_url`传递，但这不是标准的

        ``settings`` is the `Application.settings` dictionary.  ``path``
        is the static path being requested.  The url returned should be
        relative to the current host.
        `settings`是`Application.settings`的字典，`path`是请求的静态路径，
        返回的的url映射相对于强求host.

        ``include_version`` determines whether the generated URL should
        include the query string containing the version hash of the
        file corresponding to the given ``path``.
        ``include_version`` 决定生成的URL是否应该包含含有给定
        ``path`` 相对应文件的hash版本查询字符串.

        """
        url = settings.get("static_url_prefix", "/static/") + path
        if not include_version:
            return url

        version_hash = cls.get_version(settings, path)
        if not version_hash:
            return url

        return "%s?v=%s" % (url, version_hash)

    def parse_url_path(self, url_path: str) -> str:
        """Converts a static URL path into a filesystem path.

        ``url_path`` is the path component of the URL with
        ``static_url_prefix`` removed.  The return value should be
        filesystem path relative to ``static_path``.

        This is the inverse of `make_static_url`.
        """
        if os.path.sep != "/":
            url_path = url_path.replace("/", os.path.sep)
        return url_path

    @classmethod
    def get_version(cls, settings: Dict[str, Any], path: str) -> Optional[str]:
        """Generate the version string to be used in static URLs.

        ``settings`` is the `Application.settings` dictionary and ``path``
        is the relative location of the requested asset on the filesystem.
        The returned value should be a string, or ``None`` if no version
        could be determined.

        .. versionchanged:: 3.1
           This method was previously recommended for subclasses to override;
           `get_content_version` is now preferred as it allows the base
           class to handle caching of the result.
        """
        abs_path = cls.get_absolute_path(settings["static_path"], path)
        return cls._get_cached_version(abs_path)

    @classmethod
    def _get_cached_version(cls, abs_path: str) -> Optional[str]:
        with cls._lock:
            hashes = cls._static_hashes
            if abs_path not in hashes:
                try:
                    hashes[abs_path] = cls.get_content_version(abs_path)
                except Exception:
                    gen_log.error("Could not open static file %r", abs_path)
                    hashes[abs_path] = None
            hsh = hashes.get(abs_path)
            if hsh:
                return hsh
        return None


class FallbackHandler(RequestHandler):
    """A `RequestHandler` that wraps another HTTP server callback.

    The fallback is a callable object that accepts an
    `~.httputil.HTTPServerRequest`, such as an `Application` or
    `tornado.wsgi.WSGIContainer`.  This is most useful to use both
    Tornado ``RequestHandlers`` and WSGI in the same server.  Typical
    usage::

        wsgi_app = tornado.wsgi.WSGIContainer(
            django.core.handlers.wsgi.WSGIHandler())
        application = tornado.web.Application([
            (r"/foo", FooHandler),
            (r".*", FallbackHandler, dict(fallback=wsgi_app),
        ])
    """

    def initialize(
        self, fallback: Callable[[httputil.HTTPServerRequest], None]
    ) -> None:
        self.fallback = fallback

    def prepare(self) -> None:
        self.fallback(self.request)
        self._finished = True
        self.on_finish()


class OutputTransform(object):
    """A transform modifies the result of an HTTP request (e.g., GZip encoding)

    Applications are not expected to create their own OutputTransforms
    or interact with them directly; the framework chooses which transforms
    (if any) to apply.
    """

    def __init__(self, request: httputil.HTTPServerRequest) -> None:
        pass

    def transform_first_chunk(
        self,
        status_code: int,
        headers: httputil.HTTPHeaders,
        chunk: bytes,
        finishing: bool,
    ) -> Tuple[int, httputil.HTTPHeaders, bytes]:
        return status_code, headers, chunk

    def transform_chunk(self, chunk: bytes, finishing: bool) -> bytes:
        return chunk


class GZipContentEncoding(OutputTransform):
    """Applies the gzip content encoding to the response.

    See http://www.w3.org/Protocols/rfc2616/rfc2616-sec14.html#sec14.11

    .. versionchanged:: 4.0
        Now compresses all mime types beginning with ``text/``, instead
        of just a whitelist. (the whitelist is still used for certain
        non-text mime types).
    """

    # Whitelist of compressible mime types (in addition to any types
    # beginning with "text/").
    CONTENT_TYPES = set(
        [
            "application/javascript",
            "application/x-javascript",
            "application/xml",
            "application/atom+xml",
            "application/json",
            "application/xhtml+xml",
            "image/svg+xml",
        ]
    )
    # Python's GzipFile defaults to level 9, while most other gzip
    # tools (including gzip itself) default to 6, which is probably a
    # better CPU/size tradeoff.
    GZIP_LEVEL = 6
    # Responses that are too short are unlikely to benefit from gzipping
    # after considering the "Content-Encoding: gzip" header and the header
    # inside the gzip encoding.
    # Note that responses written in multiple chunks will be compressed
    # regardless of size.
    MIN_LENGTH = 1024

    def __init__(self, request: httputil.HTTPServerRequest) -> None:
        self._gzipping = "gzip" in request.headers.get("Accept-Encoding", "")

    def _compressible_type(self, ctype: str) -> bool:
        return ctype.startswith("text/") or ctype in self.CONTENT_TYPES

    def transform_first_chunk(
        self,
        status_code: int,
        headers: httputil.HTTPHeaders,
        chunk: bytes,
        finishing: bool,
    ) -> Tuple[int, httputil.HTTPHeaders, bytes]:
        # TODO: can/should this type be inherited from the superclass?
        if "Vary" in headers:
            headers["Vary"] += ", Accept-Encoding"
        else:
            headers["Vary"] = "Accept-Encoding"
        if self._gzipping:
            ctype = _unicode(headers.get("Content-Type", "")).split(";")[0]
            self._gzipping = (
                self._compressible_type(ctype)
                and (not finishing or len(chunk) >= self.MIN_LENGTH)
                and ("Content-Encoding" not in headers)
            )
        if self._gzipping:
            headers["Content-Encoding"] = "gzip"
            self._gzip_value = BytesIO()
            self._gzip_file = gzip.GzipFile(
                mode="w", fileobj=self._gzip_value, compresslevel=self.GZIP_LEVEL
            )
            chunk = self.transform_chunk(chunk, finishing)
            if "Content-Length" in headers:
                # The original content length is no longer correct.
                # If this is the last (and only) chunk, we can set the new
                # content-length; otherwise we remove it and fall back to
                # chunked encoding.
                if finishing:
                    headers["Content-Length"] = str(len(chunk))
                else:
                    del headers["Content-Length"]
        return status_code, headers, chunk

    def transform_chunk(self, chunk: bytes, finishing: bool) -> bytes:
        if self._gzipping:
            self._gzip_file.write(chunk)
            if finishing:
                self._gzip_file.close()
            else:
                self._gzip_file.flush()
            chunk = self._gzip_value.getvalue()
            self._gzip_value.truncate(0)
            self._gzip_value.seek(0)
        return chunk


def authenticated(
    method: Callable[..., Optional[Awaitable[None]]]
) -> Callable[..., Optional[Awaitable[None]]]:
    """Decorate methods with this to require that the user be logged in.

    If the user is not logged in, they will be redirected to the configured
    `login url <RequestHandler.get_login_url>`.

    If you configure a login url with a query parameter, Tornado will
    assume you know what you're doing and use it as-is.  If not, it
    will add a `next` parameter so the login page knows where to send
    you once you're logged in.
    """

    @functools.wraps(method)
    def wrapper(  # type: ignore
        self: RequestHandler, *args, **kwargs
    ) -> Optional[Awaitable[None]]:
        if not self.current_user:
            if self.request.method in ("GET", "HEAD"):
                url = self.get_login_url()
                if "?" not in url:
                    if urllib.parse.urlsplit(url).scheme:
                        # if login url is absolute, make next absolute too
                        next_url = self.request.full_url()
                    else:
                        assert self.request.uri is not None
                        next_url = self.request.uri
                    url += "?" + urlencode(dict(next=next_url))
                self.redirect(url)
                return None
            raise HTTPError(403)
        return method(self, *args, **kwargs)

    return wrapper


class UIModule(object):
    """A re-usable, modular UI unit on a page.

    UI modules often execute additional queries, and they can include
    additional CSS and JavaScript that will be included in the output
    page, which is automatically inserted on page render.

    Subclasses of UIModule must override the `render` method.
    """

    def __init__(self, handler: RequestHandler) -> None:
        self.handler = handler
        self.request = handler.request
        self.ui = handler.ui
        self.locale = handler.locale

    @property
    def current_user(self) -> Any:
        return self.handler.current_user

    def render(self, *args: Any, **kwargs: Any) -> str:
        """Override in subclasses to return this module's output."""
        raise NotImplementedError()

    def embedded_javascript(self) -> Optional[str]:
        """ 在</body>前插入一段javascript代码

        Returns: javascript代码

        """
        """Override to return a JavaScript string
        to be embedded in the page."""
        return None

    def javascript_files(self) -> Optional[Iterable[str]]:
        """ 在</body>前插入一个或多个javascript 引用

        Returns: 返回javascript路径地址集合

        """
        """Override to return a list of JavaScript files needed by this module.

        If the return values are relative paths, they will be passed to
        `RequestHandler.static_url`; otherwise they will be used as-is.
        """
        return None

    def embedded_css(self) -> Optional[str]:
        """ 在html插入一段css代码

        Returns: css代码

        """
        """Override to return a CSS string
        that will be embedded in the page."""
        return None

    def css_files(self) -> Optional[Iterable[str]]:
        """ 在</body>前插入一个或多个css 引用

        Returns: 返回css路径地址集合

        """
        """Override to returns a list of CSS files required by this module.

        If the return values are relative paths, they will be passed to
        `RequestHandler.static_url`; otherwise they will be used as-is.
        """
        return None

    def html_head(self) -> Optional[str]:
        """Override to return an HTML string that will be put in the <head/>
        element.
        """
        return None

    def html_body(self) -> Optional[str]:
        """Override to return an HTML string that will be put at the end of
        the <body/> element.
        """
        return None

    def render_string(self, path: str, **kwargs: Any) -> bytes:
        """Renders a template and returns it as a string."""
        return self.handler.render_string(path, **kwargs)


class _linkify(UIModule):
    def render(self, text: str, **kwargs: Any) -> str:  # type: ignore
        return escape.linkify(text, **kwargs)


class _xsrf_form_html(UIModule):
    def render(self) -> str:  # type: ignore
        return self.handler.xsrf_form_html()


class TemplateModule(UIModule):
    """UIModule that simply renders the given template.

    {% module Template("foo.html") %} is similar to {% include "foo.html" %},
    but the module version gets its own namespace (with kwargs passed to
    Template()) instead of inheriting the outer template's namespace.

    Templates rendered through this module also get access to UIModule's
    automatic JavaScript/CSS features.  Simply call set_resources
    inside the template and give it keyword arguments corresponding to
    the methods on UIModule: {{ set_resources(js_files=static_url("my.js")) }}
    Note that these resources are output once per template file, not once
    per instantiation of the template, so they must not depend on
    any arguments to the template.
    """

    def __init__(self, handler: RequestHandler) -> None:
        super().__init__(handler)
        # keep resources in both a list and a dict to preserve order
        self._resource_list = []  # type: List[Dict[str, Any]]
        self._resource_dict = {}  # type: Dict[str, Dict[str, Any]]

    def render(self, path: str, **kwargs: Any) -> bytes:  # type: ignore
        def set_resources(**kwargs) -> str:  # type: ignore
            if path not in self._resource_dict:
                self._resource_list.append(kwargs)
                self._resource_dict[path] = kwargs
            else:
                if self._resource_dict[path] != kwargs:
                    raise ValueError(
                        "set_resources called with different "
                        "resources for the same template"
                    )
            return ""

        return self.render_string(path, set_resources=set_resources, **kwargs)

    def _get_resources(self, key: str) -> Iterable[str]:
        return (r[key] for r in self._resource_list if key in r)

    def embedded_javascript(self) -> str:
        return "\n".join(self._get_resources("embedded_javascript"))

    def javascript_files(self) -> Iterable[str]:
        result = []
        for f in self._get_resources("javascript_files"):
            if isinstance(f, (unicode_type, bytes)):
                result.append(f)
            else:
                result.extend(f)
        return result

    def embedded_css(self) -> str:
        return "\n".join(self._get_resources("embedded_css"))

    def css_files(self) -> Iterable[str]:
        result = []
        for f in self._get_resources("css_files"):
            if isinstance(f, (unicode_type, bytes)):
                result.append(f)
            else:
                result.extend(f)
        return result

    def html_head(self) -> str:
        return "".join(self._get_resources("html_head"))

    def html_body(self) -> str:
        return "".join(self._get_resources("html_body"))


class _UIModuleNamespace(object):
    """Lazy namespace which creates UIModule proxies bound to a handler."""

    def __init__(
        self, handler: RequestHandler, ui_modules: Dict[str, Type[UIModule]]
    ) -> None:
        self.handler = handler
        self.ui_modules = ui_modules

    def __getitem__(self, key: str) -> Callable[..., str]:
        return self.handler._ui_module(key, self.ui_modules[key])

    def __getattr__(self, key: str) -> Callable[..., str]:
        try:
            return self[key]
        except KeyError as e:
            raise AttributeError(str(e))


def create_signed_value(
    secret: _CookieSecretTypes,
    name: str,
    value: Union[str, bytes],
    version: Optional[int] = None,
    clock: Optional[Callable[[], float]] = None,
    key_version: Optional[int] = None,
) -> bytes:
    if version is None:
        version = DEFAULT_SIGNED_VALUE_VERSION
    if clock is None:
        clock = time.time

    timestamp = utf8(str(int(clock())))
    value = base64.b64encode(utf8(value))
    if version == 1:
        assert not isinstance(secret, dict)
        signature = _create_signature_v1(secret, name, value, timestamp)
        value = b"|".join([value, timestamp, signature])
        return value
    elif version == 2:
        # The v2 format consists of a version number and a series of
        # length-prefixed fields "%d:%s", the last of which is a
        # signature, all separated by pipes.  All numbers are in
        # decimal format with no leading zeros.  The signature is an
        # HMAC-SHA256 of the whole string up to that point, including
        # the final pipe.
        #
        # The fields are:
        # - format version (i.e. 2; no length prefix)
        # - key version (integer, default is 0)
        # - timestamp (integer seconds since epoch)
        # - name (not encoded; assumed to be ~alphanumeric)
        # - value (base64-encoded)
        # - signature (hex-encoded; no length prefix)
        def format_field(s: Union[str, bytes]) -> bytes:
            return utf8("%d:" % len(s)) + utf8(s)

        to_sign = b"|".join(
            [
                b"2",
                format_field(str(key_version or 0)),
                format_field(timestamp),
                format_field(name),
                format_field(value),
                b"",
            ]
        )

        if isinstance(secret, dict):
            assert (
                key_version is not None
            ), "Key version must be set when sign key dict is used"
            assert version >= 2, "Version must be at least 2 for key version support"
            secret = secret[key_version]

        signature = _create_signature_v2(secret, to_sign)
        return to_sign + signature
    else:
        raise ValueError("Unsupported version %d" % version)


# A leading version number in decimal
# with no leading zeros, followed by a pipe.
_signed_value_version_re = re.compile(br"^([1-9][0-9]*)\|(.*)$")


def _get_version(value: bytes) -> int:
    # Figures out what version value is.  Version 1 did not include an
    # explicit version field and started with arbitrary base64 data,
    # which makes this tricky.
    m = _signed_value_version_re.match(value)
    if m is None:
        version = 1
    else:
        try:
            version = int(m.group(1))
            if version > 999:
                # Certain payloads from the version-less v1 format may
                # be parsed as valid integers.  Due to base64 padding
                # restrictions, this can only happen for numbers whose
                # length is a multiple of 4, so we can treat all
                # numbers up to 999 as versions, and for the rest we
                # fall back to v1 format.
                version = 1
        except ValueError:
            version = 1
    return version


def decode_signed_value(
    secret: _CookieSecretTypes,
    name: str,
    value: Union[None, str, bytes],
    max_age_days: float = 31,
    clock: Optional[Callable[[], float]] = None,
    min_version: Optional[int] = None,
) -> Optional[bytes]:
    if clock is None:
        clock = time.time
    if min_version is None:
        min_version = DEFAULT_SIGNED_VALUE_MIN_VERSION
    if min_version > 2:
        raise ValueError("Unsupported min_version %d" % min_version)
    if not value:
        return None

    value = utf8(value)
    version = _get_version(value)

    if version < min_version:
        return None
    if version == 1:
        assert not isinstance(secret, dict)
        return _decode_signed_value_v1(secret, name, value, max_age_days, clock)
    elif version == 2:
        return _decode_signed_value_v2(secret, name, value, max_age_days, clock)
    else:
        return None


def _decode_signed_value_v1(
    secret: Union[str, bytes],
    name: str,
    value: bytes,
    max_age_days: float,
    clock: Callable[[], float],
) -> Optional[bytes]:
    parts = utf8(value).split(b"|")
    if len(parts) != 3:
        return None
    signature = _create_signature_v1(secret, name, parts[0], parts[1])
    if not hmac.compare_digest(parts[2], signature):
        gen_log.warning("Invalid cookie signature %r", value)
        return None
    timestamp = int(parts[1])
    if timestamp < clock() - max_age_days * 86400:
        gen_log.warning("Expired cookie %r", value)
        return None
    if timestamp > clock() + 31 * 86400:
        # _cookie_signature does not hash a delimiter between the
        # parts of the cookie, so an attacker could transfer trailing
        # digits from the payload to the timestamp without altering the
        # signature.  For backwards compatibility, sanity-check timestamp
        # here instead of modifying _cookie_signature.
        gen_log.warning("Cookie timestamp in future; possible tampering %r", value)
        return None
    if parts[1].startswith(b"0"):
        gen_log.warning("Tampered cookie %r", value)
        return None
    try:
        return base64.b64decode(parts[0])
    except Exception:
        return None


def _decode_fields_v2(value: bytes) -> Tuple[int, bytes, bytes, bytes, bytes]:
    def _consume_field(s: bytes) -> Tuple[bytes, bytes]:
        length, _, rest = s.partition(b":")
        n = int(length)
        field_value = rest[:n]
        # In python 3, indexing bytes returns small integers; we must
        # use a slice to get a byte string as in python 2.
        if rest[n : n + 1] != b"|":
            raise ValueError("malformed v2 signed value field")
        rest = rest[n + 1 :]
        return field_value, rest

    rest = value[2:]  # remove version number
    key_version, rest = _consume_field(rest)
    timestamp, rest = _consume_field(rest)
    name_field, rest = _consume_field(rest)
    value_field, passed_sig = _consume_field(rest)
    return int(key_version), timestamp, name_field, value_field, passed_sig


def _decode_signed_value_v2(
    secret: _CookieSecretTypes,
    name: str,
    value: bytes,
    max_age_days: float,
    clock: Callable[[], float],
) -> Optional[bytes]:
    try:
        (
            key_version,
            timestamp_bytes,
            name_field,
            value_field,
            passed_sig,
        ) = _decode_fields_v2(value)
    except ValueError:
        return None
    signed_string = value[: -len(passed_sig)]

    if isinstance(secret, dict):
        try:
            secret = secret[key_version]
        except KeyError:
            return None

    expected_sig = _create_signature_v2(secret, signed_string)
    if not hmac.compare_digest(passed_sig, expected_sig):
        return None
    if name_field != utf8(name):
        return None
    timestamp = int(timestamp_bytes)
    if timestamp < clock() - max_age_days * 86400:
        # The signature has expired.
        return None
    try:
        return base64.b64decode(value_field)
    except Exception:
        return None


def get_signature_key_version(value: Union[str, bytes]) -> Optional[int]:
    value = utf8(value)
    version = _get_version(value)
    if version < 2:
        return None
    try:
        key_version, _, _, _, _ = _decode_fields_v2(value)
    except ValueError:
        return None

    return key_version


def _create_signature_v1(secret: Union[str, bytes], *parts: Union[str, bytes]) -> bytes:
    hash = hmac.new(utf8(secret), digestmod=hashlib.sha1)
    for part in parts:
        hash.update(utf8(part))
    return utf8(hash.hexdigest())


def _create_signature_v2(secret: Union[str, bytes], s: bytes) -> bytes:
    hash = hmac.new(utf8(secret), digestmod=hashlib.sha256)
    hash.update(utf8(s))
    return utf8(hash.hexdigest())


def is_absolute(path: str) -> bool:
    return any(path.startswith(x) for x in ["/", "http:", "https:"])
