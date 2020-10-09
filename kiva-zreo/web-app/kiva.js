// wonderful jquery-based KiVa client application

$(document).ready(function () {

  html = s => $("<div>").text(s).html()

  // TODO initialization
  // - set default url/path value
  // - hide application division

  /* horrible "fetch" implementation
   *
   * Query with method *method* on "#url" + *path*,
   * authentified as "#login" with password "#pass",
   * with parameters *params*, and execute *fun* on success.
   *
   * req('GET', '/store', {}, function () { … })
   * req('POST', '/store', {'key':'Calvin', 'val':'Hobbes'})
   * req('PUT', '/store/Calvin', {'val':'Hobbes'})
   */
  function req(method, path, params = {}, fun = function () {}) {

    // yuk, for testing
    params = $.extend(params, { "LOGIN": $("#login").val() })

    // yuk, authentication is managed by hand…
    let headers = {
        "Authorization": "Basic " + btoa($("#login").val() + ":" + $("#pass").val())
    }

    let url = new URL($("#url").val() + path)
    let body = null

    // yuk, params are managed by hand…
    if (method == "GET") {
      Object.keys(params).forEach(key => url.searchParams.append(key, params[key]))
    }
    else {
      body = JSON.stringify(params)
      headers["Content-Type"] = "application/json"
    }

    fetch(url, {
      method: method,
      mode: 'cors',
      headers: headers,
      body: body
    })
    .then(res => {
      if (!res.ok) { throw Error(res.statusText) }
      return res
    })
    .then(res =>
      res.headers.get('Content-Type') == 'application/json' ? res.json() : res.blob()
    )
    .then(j => fun(j))
    .catch(err => alert(err))
  }

  $('#get-version').click(function () {
    req('GET', '/version', {},
      function(data) {
        $("#version").text(html(data.commit))
      })
  })

  // TODO get post put delete list…
});
