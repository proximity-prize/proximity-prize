"""Small client for the pinned upstream publication contract. No source execution."""
import json
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid

BASE = "https://prove2.me/api/v1"


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None


class Provider:
    def __init__(self, api_key):
        self.key, self.token, self.expires = api_key, None, 0
        self.opener = urllib.request.build_opener(NoRedirect)

    def _request(self, path, body=None, headers=None):
        request = urllib.request.Request(BASE + path, data=body, headers=headers or {})
        try:
            with self.opener.open(request, timeout=30) as response:
                return json.load(response)
        except urllib.error.HTTPError as error:
            # Never expose response bodies, submitted code, or credentials in CI logs.
            raise RuntimeError(f"Prove2Me request failed (HTTP {error.code}); reconcile the checkpoint before retrying") from None
        except (OSError, ValueError):
            raise RuntimeError("Prove2Me request interrupted; reconcile the checkpoint before retrying") from None

    def headers(self):
        if time.monotonic() >= self.expires:
            result = self._request("/agent/refresh", json.dumps({"api_key": self.key}).encode(), {"Content-Type": "application/json"})
            self.token, self.expires = result["access_token"], time.monotonic() + 3300
        return {"Authorization": "Bearer " + self.token}

    def get(self, path, **query):
        return self._request(path + ("?" + urllib.parse.urlencode(query) if query else ""), headers=self.headers())

    def post(self, path, payload):
        return self._request(path, json.dumps(payload).encode(), {**self.headers(), "Content-Type": "application/json"})

    def verify(self, theorem_id, source, explanation):
        boundary = "prove2me-" + uuid.uuid4().hex
        fields = {"theorem_id": theorem_id, "proof_type": "prove", "explanation": explanation}
        body = b""
        for key, value in fields.items():
            body += f'--{boundary}\r\nContent-Disposition: form-data; name="{key}"\r\n\r\n{value}\r\n'.encode()
        body += f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain\r\n\r\n'.encode()
        body += source.encode() + f"\r\n--{boundary}--\r\n".encode()
        return self._request("/verify", body, {**self.headers(), "Content-Type": "multipart/form-data; boundary=" + boundary})

    def pages(self, path, field, **query):
        offset = 0
        while True:
            page = self.get(path, limit=100, offset=offset, **query)
            rows = page[field]
            yield from rows
            total = page.get("total", page.get("pagination", {}).get("total"))
            if total is None:
                raise ValueError("Unconfirmed provider pagination contract")
            offset += len(rows)
            if offset >= total:
                return
            if not rows:
                raise ValueError("Provider returned an incomplete page")
