Tornado Web Server
==================

.. image:: https://badges.gitter.im/Join%20Chat.svg
   :alt: Join the chat at https://gitter.im/tornadoweb/tornado
   :target: https://gitter.im/tornadoweb/tornado?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge

Tornado_cn项目基于Tornado6.1.0，主要做功能模块的中文解释，以及代码中的英文文档翻译，欢迎大家一起改进本项目。

`Tornado <http://www.tornadoweb.org>`_ is a Python web framework and
asynchronous networking library, originally developed at `FriendFeed
<http://friendfeed.com>`_.  By using non-blocking network I/O, Tornado
can scale to tens of thousands of open connections, making it ideal for
`long polling <http://en.wikipedia.org/wiki/Push_technology#Long_Polling>`_,
`WebSockets <http://en.wikipedia.org/wiki/WebSocket>`_, and other
applications that require a long-lived connection to each user.



`Tornado <http://www.tornadoweb.org>`_ 是一个python web框架和网络异步库，最早开发于 `FriendFeed <http://friendfeed.com>`_
Tornado使用非阻塞的网络I/O，可打开数万的连接，使其成为 `long polling <http://en.wikipedia.org/wiki/Push_technology#Long_Polling>`_,
`WebSockets <http://en.wikipedia.org/wiki/WebSocket>`_ 和其他应用的理想选择，且这都要给每一个用户一个长连接。

Hello, world
------------

Here is a simple "Hello, world" example web app for Tornado:

这是个简单tornado web app "Hello,world":

.. code-block:: python

    import tornado.ioloop
    import tornado.web

    class MainHandler(tornado.web.RequestHandler):
        def get(self):
            self.write("Hello, world")

    def make_app():
        return tornado.web.Application([
            (r"/", MainHandler),
        ])

    if __name__ == "__main__":
        app = make_app()
        app.listen(8888)
        tornado.ioloop.IOLoop.current().start()

This example does not use any of Tornado's asynchronous features; for
that see this `simple chat room
<https://github.com/tornadoweb/tornado/tree/stable/demos/chat>`_.

这个例子没有使用Tornado的异步特性；关于这些可阅读 `simple chat room
<https://github.com/tornadoweb/tornado/tree/stable/demos/chat>`_

Documentation
-------------

Documentation and links to additional resources are available at
https://www.tornadoweb.org
